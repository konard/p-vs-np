"""Keep the register tables shared and check finite executions of those tables."""

import itertools
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiments.issue624 import generate_register_machine as generator


def table(slot, bit):
    """Instantiate the generator's symbolic rows and apply shared state offsets."""
    rows = [generator.START]
    for base in range(1, slot + 1):
        rows.append([
            i if i[0] == "halt" else
            (i[0], str(base + (1 if i[1] == "base + 1" else 0)), i[2], i[3])
            for i in generator.SEEK
        ])
    offset = len(rows)
    rows.extend([
        [i if i[0] == "halt" else
         (i[0], str(int(i[1]) + offset),
          ("one" if bit else "zero") if i[2] == "bit" else i[2], i[3])
         for i in row]
        for row in generator.GROW
    ])
    return rows


def pop_table(slot):
    rows = table(slot, True)[:slot + 1]
    offset = len(rows)
    for row in generator.DELETE:
        output = []
        for instruction in row:
            if instruction[0] == "halt":
                output.append(instruction)
                continue
            _, target, symbol, direction = instruction
            target = int(target) + offset
            output.append(("move", str(target), symbol, direction))
        rows.append(output)
    return rows


def retarget(rows, target):
    return [[i if i[0] == "halt" else
             ("move", str(target(int(i[1]))), i[2], i[3]) for i in row]
            for row in rows]


def append(first, second):
    return first + retarget(second, lambda q: q + len(first))


def clear_table(slot):
    rows = pop_table(slot)
    return retarget(rows, lambda q: q if q < len(rows) else
                    0 if q == len(rows) else len(rows))


def word_table(slot, word):
    rows = []
    for bit in word:
        rows = append(rows, table(slot, bit))
    return rows


def repeat_table(slot, body):
    controller = pop_table(slot)
    head = retarget(controller, lambda q: q if q < len(controller) + 1 else
                    len(controller) + len(body) + 2)
    base = append(head, append(body, generator.JUMP))
    return retarget(base, lambda q: q if q < len(base) else
                    0 if q == len(base) else len(base))


def execute(rows, payload, steps):
    """A bounded execution of ordinary table instructions on a finite tape."""
    tape = ["blank", *payload]
    head = state = 0
    for charged in range(steps + 1):
        if state == len(rows):
            return charged, head, tape
        if charged == steps:
            return None
        scanned = tape[head] if head < len(tape) else "blank"
        instruction = rows[state][("blank", "zero", "one", "separator").index(scanned)]
        if instruction[0] == "halt":
            return None
        _, next_state, written, direction = instruction
        if head == len(tape):
            tape.append(written)
        else:
            tape[head] = written
        state = int(next_state)
        head += {"left": -1, "stay": 0, "right": 1}[direction]
        if head < 0:
            raise AssertionError("valid register execution crossed home")
    raise AssertionError("unreachable")


def flatten(blocks):
    return [s for block in blocks for s in
            [*("one" if b else "zero" for b in block), "separator"]]


def compile_program(registers, program):
    """Compile finite nested programs through the existing generated tables."""
    op, *args = program
    if op == "increment":
        slot, count = args
        return word_table(slot + 1, [True] * count)
    if op == "emit":
        return word_table(registers + 1, args[0])
    if op == "clear":
        return clear_table(args[0] + 1)
    if op == "literal":
        slot, pos = args
        return append(repeat_table(slot + 1, word_table(registers + 1, [True, True])),
                      word_table(registers + 1, [False, pos]))
    if op == "sequence":
        return append(compile_program(registers, args[0]), compile_program(registers, args[1]))
    if op == "loop":
        return repeat_table(args[0] + 1, compile_program(registers, args[1]))
    raise ValueError(op)


def program_semantics(program, x, registers, output):
    """Compute the charged contract independently of instruction execution."""
    registers, output = list(registers), list(output)
    op, *args = program
    blocks = [x, *([True] * v for v in registers), output]
    size = len(flatten(blocks))
    if op in ("increment", "emit"):
        if op == "increment":
            slot, count = args
            registers[slot] += count
        else:
            word = args[0]
            count = len(word)
            output += word
        return count * (2 * size + count + 3), registers, output
    if op == "sequence":
        first, registers, output = program_semantics(args[0], x, registers, output)
        second, registers, output = program_semantics(args[1], x, registers, output)
        return first + second, registers, output
    slot = args[0]
    pre = len(flatten(blocks[:slot + 1]))
    post = len(flatten(blocks[slot + 2:]))
    value = registers[slot]
    if op == "clear":
        registers[slot] = 0
        return value * (2 * pre + 4 * post + 2 * value + 7) + 2 * pre + 3, registers, output
    if op == "literal":
        registers[slot] = 0
        output += [True] * (2 * value) + [False, args[1]]
        charged = value * (6 * pre + 8 * post + 12 * value + 12) + 2 * pre + 3
        charged += 2 * (2 * (pre + post + 2 * value + 1) + 5)
        return charged, registers, output
    if op == "loop":
        charged = 0
        for remaining in range(value - 1, -1, -1):
            blocks = [x, *([True] * v for v in registers), output]
            pre = len(flatten(blocks[:slot + 1]))
            post = len(flatten(blocks[slot + 2:]))
            charged += 2 * pre + 4 * (remaining + 1 + post) + 5
            registers[slot] = remaining
            body, registers, output = program_semantics(args[1], x, registers, output)
            charged += body + 1
        blocks = [x, *([True] * v for v in registers), output]
        charged += 2 * len(flatten(blocks[:slot + 1])) + 3
        return charged, registers, output
    raise ValueError(op)


def copy_program(source, dest, scratch):
    return ("sequence", ("clear", scratch),
            ("sequence", ("loop", source,
                          ("sequence", ("increment", dest, 1), ("increment", scratch, 1))),
             ("loop", scratch, ("increment", source, 1))))


class RegisterMachineTests(unittest.TestCase):
    def check_program(self, program, x, registers, output):
        rows = compile_program(len(registers), program)
        charged, final_regs, final_out = program_semantics(program, x, registers, output)
        payload = flatten([x, *([True] * v for v in registers), output])
        result = execute(rows, payload, charged)
        self.assertIsNotNone(result)
        actual_charged, head, tape = result
        self.assertEqual((actual_charged, head), (charged, 0))
        while tape and tape[-1] == "blank":
            tape.pop()
        self.assertEqual(tape, ["blank", *flatten([x, *([True] * v for v in final_regs), final_out])])
        self.assertIsNone(execute(rows, payload, charged - 1))
        return final_regs, final_out

    def test_nested_loops_retain_payload_and_charge_every_iteration(self):
        for value, inner in itertools.product(range(3), repeat=2):
            program = ("loop", 0, ("sequence", ("increment", 1, inner),
                                  ("loop", 1, ("emit", [True, False]))))
            for x, output in itertools.product(([], [False, True]), repeat=2):
                with self.subTest(value=value, inner=inner, x=x, output=output):
                    self.assertEqual(self.check_program(program, x, [value, 0], output),
                                     ([0, 0], output + [True, False] * (value * inner)))

    def test_copy_uses_nested_compiler_and_restores_source_in_every_position(self):
        for source, dest, scratch in itertools.permutations(range(3)):
            for registers in itertools.product(range(3), repeat=3):
                for x, output in itertools.product(([], [False, True]), repeat=2):
                    with self.subTest(slots=(source, dest, scratch), registers=registers, x=x, output=output):
                        expected = list(registers)
                        expected[dest] += registers[source]
                        expected[scratch] = 0
                        self.assertEqual(self.check_program(copy_program(source, dest, scratch),
                                                            x, registers, output), (expected, output))

    def test_copy_then_literal_consumes_dynamic_identifier(self):
        for source in range(3):
            for dest in range(3):
                if source == dest:
                    continue
                scratch = 3 - source - dest
                for values in itertools.product(range(3), repeat=3):
                    for pos in (False, True):
                        program = ("sequence", copy_program(source, dest, scratch),
                                   ("sequence", ("literal", dest, pos), ("emit", [False, False])))
                        identifier = values[source] + values[dest]
                        expected = list(values)
                        expected[dest] = expected[scratch] = 0
                        with self.subTest(slots=(source, dest, scratch), values=values, pos=pos):
                            self.assertEqual(self.check_program(program, [False, True], values, [False]),
                                             (expected, [False] + [True] * (2 * identifier) +
                                              [False, pos, False, False]))

    def test_checked_in_tables_match_generator(self):
        generator.generate(check=True)

    def test_drift_is_rejected_and_proofs_are_preserved(self):
        for changed, extension in (("lean", "lean"), ("rocq", "v")):
            with self.subTest(prover=changed), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                with patch.object(generator, "ROOT", root):
                    for prover, suffix in (("lean", "lean"), ("rocq", "v")):
                        path = root / f"proofs/experiments/issue624/{prover}/RegisterMachine.{suffix}"
                        path.parent.mkdir(parents=True)
                        path.write_text(generator.MARKERS[prover] + f"\n{prover} proof tail\n")
                    generator.generate()
                    generator.generate(check=True)
                    path = root / f"proofs/experiments/issue624/{changed}/RegisterMachine.{extension}"
                    original = path.read_text()
                    path.write_text(original.replace("move 4", "move 5", 1))
                    with self.assertRaisesRegex(SystemExit, f"{changed}/RegisterMachine"):
                        generator.generate(check=True)
                    generator.generate()
                    self.assertEqual(path.read_text(), original)
                    self.assertTrue(path.read_text().endswith(f"{changed} proof tail\n"))

    def test_all_small_blocks_preserve_every_symbol_and_charge_exactly(self):
        words = [list(bits) for size in range(3)
                 for bits in itertools.product((False, True), repeat=size)]
        # 2,058 executions; every input, register and output has at most 2 bits.
        for blocks in itertools.product(words, repeat=3):
            payload = flatten(blocks)
            cost = 2 * len(payload) + 4
            for slot in range(3):
                for bit in (False, True):
                    with self.subTest(blocks=blocks, slot=slot, bit=bit):
                        changed = [*blocks]
                        changed[slot] = [*blocks[slot], bit]
                        rows = table(slot, bit)
                        self.assertEqual(execute(rows, payload, cost),
                                         (cost, 0, ["blank", *flatten(changed)]))
                        self.assertIsNone(execute(rows, payload, cost - 1))

    def test_invalid_slot_rejects(self):
        self.assertIsNone(execute(table(3, True), flatten([[], [], []]), 30))

    def test_clear_charges_exactly_and_retains_all_surrounding_symbols(self):
        words = [list(bits) for size in range(3)
                 for bits in itertools.product((False, True), repeat=size)]
        for before, after in itertools.product(words, repeat=2):
            for value in range(4):
                blocks = [before, [True] * value, after]
                pre = len(flatten([before]))
                post = len(flatten([after]))
                cost = value * (2 * pre + 4 * post + 2 * value + 7) + 2 * pre + 3
                rows = clear_table(1)
                expected = ["blank", *flatten([before, [], after])]
                if value:
                    expected += ["blank"] * (value + 1)
                with self.subTest(before=before, after=after, value=value):
                    self.assertEqual(execute(rows, flatten(blocks), cost),
                                     (cost, 0, expected))
                    self.assertIsNone(execute(rows, flatten(blocks), cost - 1))
                    self.assertLessEqual(cost, 10 * (pre + value + post + 2) ** 2)

    def test_clear_rejects_non_unary_register_and_invalid_slot(self):
        for value in ([False], [True, False], [True, True, False]):
            with self.subTest(value=value):
                self.assertIsNone(execute(clear_table(1), flatten([[], value, []]), 100))
        self.assertIsNone(execute(clear_table(3), flatten([[], [], []]), 100))

    def test_dynamic_ticks_emit_exact_unary_identifiers_and_charge_the_jump(self):
        words = [list(bits) for size in range(3)
                 for bits in itertools.product((False, True), repeat=size)]
        # 588 finite cases cover every register position and both-bit payloads.
        for before, after in itertools.product(words, repeat=2):
            for slot in range(3):
                for value in range(4):
                    registers = [[True], [], [True, True]]
                    registers[slot] = [True] * value
                    blocks = [before, *registers, after]
                    pre = len(flatten(blocks[:slot + 1]))
                    post = len(flatten(blocks[slot + 2:]))
                    charged = value * (6 * pre + 8 * post + 12 * value + 12) + 2 * pre + 3
                    rows = repeat_table(slot + 1, word_table(4, [True, True]))
                    final = [before, *registers, after + [True] * (2 * value)]
                    final[slot + 1] = []
                    with self.subTest(before=before, after=after, slot=slot, value=value):
                        result = execute(rows, flatten(blocks), charged)
                        self.assertIsNotNone(result)
                        steps, head, tape = result
                        self.assertEqual((steps, head), (charged, 0))
                        while tape and tape[-1] == "blank":
                            tape.pop()
                        self.assertEqual(tape, ["blank", *flatten(final)])
                        self.assertIsNone(execute(rows, flatten(blocks), charged - 1))
                        self.assertLessEqual(charged, 20 * (pre + value + post + 1) ** 2)

    def test_repeat_empty_body_and_malformed_counter(self):
        rows = repeat_table(1, [])
        self.assertEqual(execute(rows, flatten([[False], [], [True]]), 7),
                         (7, 0, ["blank", *flatten([[False], [], [True]])]))
        self.assertIsNone(execute(rows, flatten([[False], [True, False], [True]]), 100))

    def test_dynamic_literal_includes_delimiter_and_both_polarities(self):
        # Identifiers come from the tape; one fixed table handles all values.
        for slot in range(3):
            for positive in (False, True):
                rows = append(repeat_table(slot + 1, word_table(4, [True, True])),
                              word_table(4, [False, positive]))
                for value in range(5):
                    registers = [[True], [], [True, True]]
                    registers[slot] = [True] * value
                    blocks = [[False, True], *registers, [False]]
                    pre = len(flatten(blocks[:slot + 1]))
                    post = len(flatten(blocks[slot + 2:]))
                    ticks_cost = value * (6 * pre + 8 * post + 12 * value + 12) + 2 * pre + 3
                    charged = ticks_cost + 2 * (2 * (pre + post + 2 * value + 1) + 5)
                    expected = [list(block) for block in blocks]
                    expected[slot + 1] = []
                    expected[-1] += [True] * (2 * value) + [False, positive]
                    with self.subTest(slot=slot, positive=positive, value=value):
                        result = execute(rows, flatten(blocks), charged)
                        self.assertIsNotNone(result)
                        steps, head, tape = result
                        self.assertEqual((steps, head), (charged, 0))
                        while tape and tape[-1] == "blank":
                            tape.pop()
                        self.assertEqual(tape, ["blank", *flatten(expected)])
                        self.assertIsNone(execute(rows, flatten(blocks), charged - 1))
                        self.assertLessEqual(charged, 40 * (pre + value + post + 1) ** 2)

    def test_public_theorem_names_match(self):
        import re

        root = generator.ROOT / "proofs/experiments/issue624"
        lean = (root / "lean/RegisterMachine.lean").read_text()
        rocq = (root / "rocq/RegisterMachine.v").read_text()
        self.assertEqual(set(re.findall(r"\btheorem (\w+)", lean)),
                         set(re.findall(r"\bTheorem (\w+)", rocq)))


if __name__ == "__main__":
    unittest.main()
