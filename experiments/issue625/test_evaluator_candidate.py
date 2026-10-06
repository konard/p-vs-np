"""Bounded experiments for a prospective circuit-evaluation instruction table.

These checks compare actual charged machine instructions with the circuit
specification. They do not replace a universally quantified prover theorem.
"""

import itertools
import unittest

from experiments.issue625.evaluator_candidate import (
    enc_circuit,
    run_machine,
    verify_circuit,
)


class EvaluatorCandidateTests(unittest.TestCase):
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


if __name__ == '__main__':
    unittest.main()
