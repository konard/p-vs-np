#!/usr/bin/env python3
"""Kernel-check circuit-evaluator runs and universal phase invariants.

The generated table must equal the certified verifier table. This checks
concrete runs, universal proof assumptions, and four invalid machine mutations.
"""

import argparse
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from experiments.issue567.check_machines import compile_probe
from experiments.issue625.evaluator_candidate import (
    BLANK, RIGHT, LEFT, Halt, Move, STATES, STATE_INDEX, TABLE, enc_circuit, run_machine,
)
from scripts import check_proof_status as proof_status


AUDITED_THEOREMS = (
    'execute_sound', 'execute_complete', 'nand_false_run', 'nand_true_run',
    'dependent_gate_run', 'forward_wire_run', 'lookup_first_initial',
    'malformed_reject', 'valid_start', 'gate_empty_run', 'count_success', 'count_reject',
)
CERTIFIED_THEOREMS = (
    'lookup_advance', 'lookup_short', 'lookup_read', 'lookup_initial', 'lookup_empty',
    'lookup_tail_success', 'lookup_tail_reject', 'lookup_success', 'lookup_reject',
    'append_gate', 'gate_empty_padded', 'gate_step', 'gate_reject', 'gate_loop', 'verifier_run',
    'verifier_correct', 'verifier_accepts',
)
AUDITED_THEOREMS += CERTIFIED_THEOREMS


def audit_reports(language, output):
    """Check every printed report, including reports after an allowed one."""
    if language == 'lean':
        reports = dict(re.findall(
            r"(?m)^'(?:Issue625\.EvaluatorCandidate|Issue532\.CircuitVerifier)\.(\w+)' (.+)$", output,
        ))
        for name in AUDITED_THEOREMS:
            if name not in reports:
                raise ValueError(f'lean: missing assumption report for {name}')
            assumptions = proof_status.parse_lean_axioms(reports[name])
            forbidden = assumptions - {'propext', 'Classical.choice', 'Quot.sound'}
            if forbidden:
                raise ValueError(f'lean: {name} uses unapproved assumptions: {sorted(forbidden)}')
    elif language == 'rocq':
        # Rocq prints no theorem name for a closed context. Reject any open
        # context before counting closed ones; one closed result is insufficient.
        if 'Axioms:' in output:
            raise ValueError('rocq: candidate results have global assumptions')
        if output.count('Closed under the global context') != len(AUDITED_THEOREMS):
            raise ValueError('rocq: missing candidate assumption reports')
    else:
        raise ValueError(f'unknown prover: {language}')


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


def table_source(language, program=TABLE):
    symbols = ['blank', 'zero', 'one', 'separator']
    directions = {-1: 'left', 0: 'stay', 1: 'right'}
    rows = []
    for index, (state, row) in enumerate(zip(STATES, program)):
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
    invariants = (HERE / f'EvaluatorInvariants{suffix}.in').read_text(encoding='utf-8')
    invariants += '\n' + (HERE / f'LengthInvariants{suffix}.in').read_text(encoding='utf-8')
    source = template.replace('@TABLE@', table_source(language)).replace('@EXAMPLES@', examples_source(language))
    source = source.replace('@INVARIANTS@', invariants)
    for state, index in STATE_INDEX.items():
        source = source.replace(f'@STATE_{state}@', str(index))
    if language == 'lean':
        certified = 'example : candidate = Issue532.CircuitVerifier.candidate := by rfl\n'
        certified += '\n'.join('#print axioms Issue532.CircuitVerifier.' + n for n in CERTIFIED_THEOREMS)
        source = source.replace('end Issue625.EvaluatorCandidate', certified + '\nend Issue625.EvaluatorCandidate')
    else:
        certified = 'Example certified_table : candidate = CircuitVerifier.candidate.\nProof. reflexivity. Qed.\n'
        certified += '\n'.join('Print Assumptions CircuitVerifier.' + n + '.' for n in CERTIFIED_THEOREMS)
        source = source.replace('End EvaluatorCandidate.', certified + '\nEnd EvaluatorCandidate.')
    return source


def machine_mutations():
    """Each finite witness distinguishes a bad machine from verifyCircuit."""
    wrong_length = [row.copy() for row in TABLE]
    wrong_length[STATE_INDEX['start_left']][BLANK] = Move('advance_second', BLANK, RIGHT)
    forward_wire = [row.copy() for row in TABLE]
    forward_wire[STATE_INDEX['lookup_first_mark_next']][BLANK] = Move('lookup_first_back_sep', BLANK, LEFT)
    return {
        'zero_step': (TABLE, [], [], [], True),
        'ignore_certificate': (TABLE, enc_circuit(1, []), [True], [False], False),
        'wrong_length': (wrong_length, enc_circuit(1, []), [True, True], [True, True], False),
        'forward_wire': (forward_wire, enc_circuit(1, [(1, 0)]), [True], [True], False),
    }


def check_mutations(language, logs):
    suffix = '.lean' if language == 'lean' else '.v'
    template = (HERE / f'EvaluatorCandidate{suffix}.in').read_text()
    template = re.sub(r'(?m)^#print axioms .*\n|^Print Assumptions .*\n', '', template)
    with tempfile.TemporaryDirectory(prefix='verifier_mutations_', dir=HERE) as directory:
        for name, (program, word, cert, supplied, zero_step) in machine_mutations().items():
            w = list_source([bool_source(b) for b in word], language)
            c = list_source([bool_source(b) for b in cert], language)
            actual = list_source([bool_source(b) for b in supplied], language)
            steps = 0 if zero_step else run_machine(word, supplied, program=program).steps
            if language == 'lean':
                proof = 'by\n  apply Run.halt\n  rfl' if zero_step else (
                    f'execute_sound candidate {steps} _ _ _ (by decide)')
                witness = f'example : Run candidate (pairedInput {w} {actual}) {steps} (verifyCircuit {w} {c}) :=\n  {proof}\n'
            else:
                proof = 'apply run_halt. reflexivity.' if zero_step else (
                    f'apply (execute_sound candidate {steps}). vm_compute. reflexivity.')
                witness = f'Example mutation : Run candidate (pairedInput {w} {actual}) {steps} (verifyCircuit {w} {c}).\nProof. {proof} Qed.\n'
            source = template.replace('@TABLE@', table_source(language, program)).replace('@EXAMPLES@', witness).replace('@INVARIANTS@', '')
            path = Path(directory) / ('Mutation_' + name + suffix)
            path.write_text(source)
            result = compile_probe(language, path, logs / f'{language}-machine-{name}.log',
                                   extra_args=('-j', '2', '-M', '1024') if language == 'lean' else ())
            output = result.stdout + result.stderr
            expected = ('could not unify the conclusion of `@Run.halt`' if zero_step else
                        'Tactic `decide` proved that the proposition') if language == 'lean' else 'Unable to unify'
            if result.returncode == 0 or expected not in output:
                raise RuntimeError(f'{language}: mutation {name} failed unexpectedly or was accepted; see {logs}')
            print(f'{language}: rejected actual verifier mutation {name}')


def check(language):
    logs = HERE / 'logs'
    logs.mkdir(exist_ok=True)
    suffix = '.lean' if language == 'lean' else '.v'
    source = probe_source(language)
    (logs / f'{language}-evaluator-candidate{suffix}.in').write_text(source, encoding='utf-8')
    with tempfile.TemporaryDirectory(prefix='evaluator_candidate_', dir=HERE) as directory:
        path = Path(directory) / f'EvaluatorCandidate{suffix}'
        path.write_text(source, encoding='utf-8')
        entries = [{'source': str(path.relative_to(ROOT))}]
        failures = proof_status.check_sources(ROOT, proof_status.source_closure(ROOT, entries))
        if failures:
            raise RuntimeError('\n'.join(failures))
        log = logs / f'{language}-evaluator-candidate.log'
        extra_args = ('-j', '2', '-M', '1024') if language == 'lean' else ()
        result = compile_probe(language, path, log, extra_args=extra_args)
        if result.returncode:
            raise RuntimeError(f'{language}: evaluator probe failed; see {log}\n'
                               + (result.stdout + result.stderr).rstrip())
        audit_reports(language, result.stdout + result.stderr)
    check_mutations(language, logs)
    print(f'{language}: certified 83-state table, {len(CASES) + len(RAW_CASES)} concrete runs '
          'and universal polynomial verifier proof checked')


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
