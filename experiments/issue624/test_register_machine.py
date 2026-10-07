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


class RegisterMachineTests(unittest.TestCase):
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

    def test_public_theorem_names_match(self):
        import re

        root = generator.ROOT / "proofs/experiments/issue624"
        lean = (root / "lean/RegisterMachine.lean").read_text()
        rocq = (root / "rocq/RegisterMachine.v").read_text()
        self.assertEqual(set(re.findall(r"\btheorem (\w+)", lean)),
                         set(re.findall(r"\bTheorem (\w+)", rocq)))


if __name__ == "__main__":
    unittest.main()
