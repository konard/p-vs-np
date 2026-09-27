"""Regression checks for the overclaimed refutations in issue #580."""

from pathlib import Path
import re
import unittest
from itertools import product

from projector_witness import edge, matching, rank_of_incidence, reachable_from


ROOT = Path(__file__).resolve().parents[2]
ATTEMPTS = ROOT / "proofs" / "attempts"


class SemanticCoverageTests(unittest.TestCase):
    def test_projector_witness_meets_gamma_conditions_and_rank_varies(self):
        matchings = [matching(bits) for bits in product(range(2), repeat=3)]
        self.assertEqual(len(set(matchings)), 8)
        for u in range(6):
            self.assertEqual(reachable_from(u), set(range(6)))
            self.assertEqual(sum(edge(u, v) for v in range(6)), 2)
            self.assertEqual(sum(edge(v, u) for v in range(6)), 2)
        for m in matchings:
            self.assertEqual(set(m), set(range(6)))
            self.assertTrue(all(edge(u, m[u]) for u in range(6)))
        self.assertEqual({rank_of_incidence(m) for m in matchings}, {4, 5})

    def test_projector_has_three_four_cycle_components(self):
        for component in range(3):
            left = {u for u in range(6) if u // 2 == component}
            right = {v for v in range(6) if (v // 2 + 2) % 3 == component}
            self.assertEqual(len(left), 2)
            self.assertEqual(len(right), 2)
            for u in left:
                for v in range(6):
                    self.assertEqual(edge(u, v), v in right,
                                     msg=f"component={component}, edge=({u}, {v})")
            self.assertEqual(sum(edge(u, v) for u in left for v in right), 4)
        self.assertGreater(3, 6 // 4)

    def test_named_refutations_do_not_prove_truth_as_failure(self):
        for path in (
            ATTEMPTS / "guohun-zhu-2007-peqnp/refutation/lean/ZhuRefutation.lean",
            ATTEMPTS / "matt-groff-2011-peqnp/refutation/lean/GroffRefutation.lean",
            ATTEMPTS / "author104-2015-peqnp/refutation/lean/VegaRefutation.lean",
        ):
            with self.subTest(path=path.name):
                source = path.read_text()
                self.assertNotRegex(source, r"(?s)theorem\s+\w+[^:]*:\s*(?:--[^\n]*\n\s*)*True\s*:=")
                self.assertNotRegex(source, r"\b(?:sorry|axiom)\b")

        for path in (
            ATTEMPTS / "guohun-zhu-2007-peqnp/refutation/rocq/ZhuRefutation.v",
            ATTEMPTS / "matt-groff-2011-peqnp/refutation/rocq/GroffRefutation.v",
            ATTEMPTS / "author104-2015-peqnp/refutation/rocq/VegaRefutation.v",
        ):
            with self.subTest(path=path.name):
                source = path.read_text()
                self.assertNotRegex(source, r"\b(?:Axiom|Admitted|admit)\b")
                self.assertNotRegex(source, r":\s*True\s*\.")

    def test_catalog_labels_every_result(self):
        source = (ATTEMPTS / "COMMON_ERRORS.md").read_text()
        rows = re.findall(r"^\| \[([^]]+)\]\([^)]*\) \|([^\n]*)$", source, re.M)
        self.assertGreater(len(rows), 100)
        allowed = (
            "Concrete refutation",
            "Conditional result",
            "Identified gap",
            "Informal/unverified analysis",
        )
        for attempt, rest in rows:
            with self.subTest(attempt=attempt):
                self.assertEqual(sum(f"| {label} |" in rest for label in allowed), 1)


if __name__ == "__main__":
    unittest.main()
