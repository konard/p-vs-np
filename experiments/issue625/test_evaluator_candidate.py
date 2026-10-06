"""Bounded regressions for the certified circuit-evaluation instruction table.

These checks compare actual charged machine instructions with the circuit
specification. They do not replace a universally quantified prover theorem.
"""

import contextlib
import io
import itertools
import json
import unittest

from experiments.issue625.evaluator_candidate import (
    BLANK, ZERO, ONE, SEPARATOR,
    enc_circuit,
    run_machine,
    verify_circuit,
)
from experiments.issue625.check_evaluator_candidate import (
    AUDITED_THEOREMS, audit_reports, machine_mutations,
)


class EvaluatorCandidateTests(unittest.TestCase):
    def test_mutations_disagree_with_verifier(self):
        for name, (program, word, cert, supplied, zero_step) in machine_mutations().items():
            with self.subTest(mutation=name):
                result = run_machine(word, supplied, program=program)
                if zero_step:
                    self.assertGreater(result.steps, 0)
                else:
                    self.assertNotEqual(result.answer, verify_circuit(word, cert))

    def check_pair(self, word, certificate):
        result = run_machine(word, certificate)
        self.assertEqual(result.answer, verify_circuit(word, certificate),
                         (word, certificate, result))
        self.assertLessEqual(result.steps, 128 * (len(word) + len(certificate) + 2) ** 2)

    def test_empty_and_identity_circuits(self):
        for n in range(4):
            for length in range(5):
                for certificate in itertools.product((False, True), repeat=length):
                    self.check_pair(enc_circuit(n, []), certificate)

    def test_nand_and_forward_wires(self):
        for n in range(3):
            for gate in itertools.product(range(4), repeat=2):
                for length in range(4):
                    for certificate in itertools.product((False, True), repeat=length):
                        self.check_pair(enc_circuit(n, [gate]), certificate)

    def test_two_gate_dependencies(self):
        for n in range(1, 3):
            for first in itertools.product(range(n), repeat=2):
                for second in itertools.product(range(n + 2), repeat=2):
                    for certificate in itertools.product((False, True), repeat=n):
                        self.check_pair(enc_circuit(n, [first, second]), certificate)

    def test_malformed_words(self):
        for length in range(9):
            for word in itertools.product((False, True), repeat=length):
                for certificate in ((), (False,), (True,), (True, False)):
                    self.check_pair(word, certificate)

    def test_longer_wire_lookups(self):
        for n in (1, 2, 8, 16):
            gates = [(0, n - 1), (n, n), (n + 1, 0)]
            for certificate in ([False] * n, [True] * n, [i % 2 == 0 for i in range(n)]):
                self.check_pair(enc_circuit(n, gates), certificate)

    def test_certificate_match_preserves_tape_and_rejects_wrong_lengths(self):
        for n in range(5):
            for gates in ([], [(0, 0)], [(0, 0), (n, 0)]):
                word = enc_circuit(n, gates)
                payload = word[n + 1:]
                for length in range(6):
                    for certificate in ([False] * length, [True] * length,
                                        [i % 2 == 0 for i in range(length)]):
                        with self.subTest(n=n, gates=gates, certificate=certificate):
                            trace = io.StringIO()
                            with contextlib.redirect_stdout(trace):
                                run_machine(word, certificate, trace=True)
                            snapshots = [json.loads(line) for line in trace.getvalue().splitlines()]
                            start = next(s for s in snapshots if s['state'] == 'count_first')
                            gate = next((s for s in snapshots if s['state'] == 'gate'), None)
                            budget = 64 * (n + 1) * (n + len(payload) + length + 4)
                            if length == n:
                                self.assertIsNotNone(gate)
                                self.assertLessEqual(gate['step'] - start['step'], budget)
                                self.assertEqual(gate['left'], [BLANK] + [ONE] * n + [ZERO])
                                self.assertEqual([gate['head']] + gate['right'],
                                                 [ONE if b else ZERO for b in payload] +
                                                 [SEPARATOR] + [ONE if b else ZERO for b in certificate] +
                                                 [BLANK])
                            else:
                                self.assertIsNone(gate)
                                self.assertLessEqual(snapshots[-1]['step'] - start['step'] + 1, budget)


class CandidateAssumptionTests(unittest.TestCase):
    def lean_reports(self, overrides=None):
        overrides = overrides or {}
        return '\n'.join(
            f"'Issue625.EvaluatorCandidate.{name}' depends on axioms: "
            f"[{overrides.get(name, 'propext, Quot.sound')}]"
            for name in AUDITED_THEOREMS
        )

    def test_permitted_reports_pass(self):
        audit_reports('lean', self.lean_reports())
        audit_reports('rocq', 'Closed under the global context\n' * len(AUDITED_THEOREMS))

    def test_later_lean_admission_rejected(self):
        with self.assertRaisesRegex(ValueError, 'gate_empty_run uses unapproved assumptions'):
            audit_reports('lean', self.lean_reports({'gate_empty_run': 'propext, sorryAx'}))

    def test_certificate_phase_admission_rejected(self):
        with self.assertRaisesRegex(ValueError, 'count_success uses unapproved assumptions'):
            audit_reports('lean', self.lean_reports({'count_success': 'sorryAx'}))

    def test_whole_verifier_admission_rejected(self):
        with self.assertRaisesRegex(ValueError, 'verifier_run uses unapproved assumptions'):
            audit_reports('lean', self.lean_reports({'verifier_run': 'sorryAx'}))

    def test_missing_lean_report_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing assumption report'):
            audit_reports('lean', self.lean_reports().split('\n', 1)[1])

    def test_rocq_mixed_closed_and_open_context_rejected(self):
        output = 'Closed under the global context\n' * len(AUDITED_THEOREMS)
        with self.assertRaisesRegex(ValueError, 'global assumptions'):
            audit_reports('rocq', output + 'Axioms:\nmissing_run : True\n')

    def test_missing_rocq_report_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing candidate assumption reports'):
            audit_reports('rocq', 'Closed under the global context\n')


if __name__ == '__main__':
    unittest.main()
