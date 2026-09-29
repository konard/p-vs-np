"""Regression guard for the Plotnikov refutation's trusted assumptions."""

from pathlib import Path
import unittest


ATTEMPT = Path(__file__).resolve().parents[2] / "proofs/attempts/anatoly-plotnikov-2007-peqnp/refutation"


class RefutationConsistencyTest(unittest.TestCase):
    def test_lean_refutation_has_no_unproved_facts(self):
        source = (ATTEMPT / "lean/PlotnikovRefutation.lean").read_text()
        self.assertNotRegex(source, r"(?m)^\s*(?:axiom|sorry|admit)\b")

    def test_rocq_refutation_has_no_unproved_facts(self):
        source = (ATTEMPT / "rocq/PlotnikovRefutation.v").read_text()
        self.assertNotRegex(source, r"(?m)^\s*(?:Axiom|Admitted|admit)\b")


if __name__ == "__main__":
    unittest.main()
