#!/usr/bin/env python3
"""Kernel-check concrete circuit-evaluator runs in the unchanged machine model.

This candidate still needs its universal evaluator theorem and polynomial
bound. Passing this script cannot satisfy the CircuitSAT completion gate.
"""

import argparse
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from experiments.issue567.check_machines import compile_probe
from experiments.issue625.evaluator_candidate import (
    Halt, STATES, STATE_INDEX, TABLE, enc_circuit, run_machine,
)


CASES = (
    ('empty_run', 0, [], []),
    ('identity_true_run', 1, [], [True]),
    ('identity_false_run', 1, [], [False]),
    ('nand_false_run', 1, [(0, 0)], [False]),
    ('nand_true_run', 1, [(0, 0)], [True]),
    ('dependent_gate_run', 2, [(0, 1), (2, 2)], [True, False]),
    ('forward_wire_run', 1, [(1, 0)], [True]),
    ('short_certificate_run', 2, [(0, 1)], [True]),
    ('long_certificate_run', 1, [(0, 0)], [True, False]),
    ('empty_certificate_run', 1, [(0, 0)], []),
    ('zero_input_gate_run', 0, [(0, 0)], []),
)
RAW_CASES = (
    ('truncated_run', [True, False, True, False], [True]),
    ('empty_word_run', [], []),
    ('trailing_bits_run', enc_circuit(1, [(0, 0)]) + [True], [False]),
)


def list_source(values, language):
    delimiter = ', ' if language == 'lean' else '; '
    return '[' + delimiter.join(values) + ']'


def bool_source(value):
    return 'true' if value else 'false'


def table_source(language):
    symbols = ['blank', 'zero', 'one', 'separator']
    directions = {-1: 'left', 0: 'stay', 1: 'right'}
    rows = []
    for index, (state, row) in enumerate(zip(STATES, TABLE)):
        instructions = []
        for instruction in row:
            if isinstance(instruction, Halt):
                expression = ('Instruction.halt' if language == 'lean' else 'halt') + ' ' + bool_source(instruction.answer)
            else:
                constructor = 'Instruction.move' if language == 'lean' else 'move'
                symbol = ('.' if language == 'lean' else '') + symbols[instruction.write]
                direction = ('.' if language == 'lean' else '') + directions[instruction.direction]
                expression = f'{constructor} {STATE_INDEX[instruction.state]} {symbol} {direction}'
            instructions.append(expression)
        delimiter = (',' if language == 'lean' else ';') if index < len(TABLE) - 1 else ''
        comment = f'-- {state}' if language == 'lean' else f'(* {state} *)'
        rows.append('    ' + list_source(instructions, language) + delimiter + ' ' + comment)
    body = '\n'.join(rows)
    if language == 'lean':
        return 'def candidate : Machine := ⟨[\n' + body + '\n]⟩\n\nexample : candidate.program.length = 83 := by decide'
    return 'Definition candidate : Machine := {| program := [\n' + body + '\n] |}.\n\nExample finite_table : length (program candidate) = 83.\nProof. reflexivity. Qed.'


def examples_source(language):
    examples = []
    cases = [(name, enc_circuit(n, gates), certificate) for name, n, gates, certificate in CASES] + list(RAW_CASES)
    for name, word, certificate in cases:
        result = run_machine(word, certificate)
        w = list_source([bool_source(bit) for bit in word], language)
        c = list_source([bool_source(bit) for bit in certificate], language)
        if language == 'lean':
            examples.append(f'theorem {name} : Run candidate (pairedInput {w} {c})\n'
                            f'    {result.steps} (verifyCircuit {w} {c}) :=\n'
                            f'  execute_sound candidate {result.steps} _ _ _ (by decide)')
        else:
            examples.append(f'Theorem {name} : Run candidate (pairedInput {w} {c})\n'
                            f'  {result.steps} (verifyCircuit {w} {c}).\nProof.\n'
                            f'  apply (execute_sound candidate {result.steps}).\n'
                            '  vm_compute. reflexivity.\nQed.')
    return '\n\n'.join(examples)


def probe_source(language):
    suffix = '.lean' if language == 'lean' else '.v'
    template = (HERE / f'EvaluatorCandidate{suffix}.in').read_text(encoding='utf-8')
    return template.replace('@TABLE@', table_source(language)).replace('@EXAMPLES@', examples_source(language))


def check(language):
    logs = HERE / 'logs'
    logs.mkdir(exist_ok=True)
    suffix = '.lean' if language == 'lean' else '.v'
    source = probe_source(language)
    (logs / f'{language}-evaluator-candidate{suffix}.in').write_text(source, encoding='utf-8')
    with tempfile.TemporaryDirectory(prefix='evaluator_candidate_', dir=HERE) as directory:
        path = Path(directory) / f'EvaluatorCandidate{suffix}'
        path.write_text(source, encoding='utf-8')
        log = logs / f'{language}-evaluator-candidate.log'
        extra_args = ('-j', '2', '-M', '1024') if language == 'lean' else ()
        result = compile_probe(language, path, log, extra_args=extra_args)
        if result.returncode:
            raise RuntimeError(f'{language}: concrete evaluator run failed; see {log}\n'
                               + (result.stdout + result.stderr).rstrip())
    print(f'{language}: 83-state candidate, {len(CASES) + len(RAW_CASES)} concrete runs checked; universal proof pending')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    parser.add_argument('--rocq', action='store_true')
    args = parser.parse_args()
    selected = [language for language in ('lean', 'rocq') if getattr(args, language)]
    for language in selected or ['lean', 'rocq']:
        check(language)


if __name__ == '__main__':
    main()
