"""Regression tests for issue #587.

The Kardash refutation said that unit propagation and arc consistency decide
2-SAT, credited that to Krom, and recorded it as an axiom of type ``True``.
These tests keep the two counterexamples from the issue, compare the
procedures with brute force, and check that the sources no longer make the
claim.
"""

import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

import kardash_2sat as k2  # noqa: E402

ATTEMPT = ROOT / "proofs" / "attempts" / "sergey-kardash-2011-peqnp"
LEAN = ATTEMPT / "refutation" / "lean" / "KardashRefutation.lean"
ROCQ = ATTEMPT / "refutation" / "rocq" / "KardashRefutation.v"
WORKFLOW = ROOT / ".github" / "workflows" / "verification.yml"
# The paper reconstruction is historical source material and is not audited.
EXPLANATIONS = [
    ATTEMPT / "README.md",
    ATTEMPT / "refutation" / "README.md",
    ATTEMPT / "proof" / "README.md",
    ATTEMPT / "proof" / "lean" / "KardashProof.lean",
    ATTEMPT / "proof" / "rocq" / "KardashProof.v",
    LEAN,
    ROCQ,
]

X, Y, Z = k2.X, k2.Y, k2.Z


class UnitPropagationCounterexample(unittest.TestCase):
    formula = k2.UP_COUNTEREXAMPLE

    def test_is_the_formula_from_the_issue(self):
        # (x or y) and (x or not y) and (not x or y) and (not x or not y)
        self.assertEqual(
            self.formula,
            [((X, False), (Y, False)), ((X, False), (Y, True)),
             ((X, True), (Y, False)), ((X, True), (Y, True))],
        )
        self.assertTrue(all(len(clause) == 2 for clause in self.formula))

    def test_every_assignment_falsifies_a_clause(self):
        self.assertFalse(k2.brute_force_sat(self.formula))

    def test_unit_propagation_reaches_a_fixpoint(self):
        self.assertEqual(k2.unit_propagate(self.formula), ("fixpoint", {}))

    def test_clausewise_arc_consistency_removes_nothing(self):
        domains = k2.arc_consistency(k2.clausewise_csp(self.formula), [X, Y])
        self.assertEqual(domains, {X: [False, True], Y: [False, True]})

    def test_a_decision_is_needed_before_propagation_conflicts(self):
        self.assertEqual(k2.unit_propagate(self.formula, {X: True})[0], "conflict")
        self.assertEqual(k2.unit_propagate(self.formula, {X: False})[0], "conflict")

    def test_implication_graph_has_a_contradictory_cycle(self):
        self.assertEqual(
            k2.implication_path(self.formula, (X, False), (X, True)),
            [(X, False), (Y, False), (X, True)],
        )
        self.assertEqual(
            k2.implication_path(self.formula, (X, True), (X, False)),
            [(X, True), (Y, False), (X, False)],
        )
        self.assertFalse(k2.scc_2sat(self.formula))


class DisequalityTriangle(unittest.TestCase):
    def test_arc_consistent_with_full_domains(self):
        domains = k2.arc_consistency(k2.TRIANGLE_CSP, [X, Y, Z])
        self.assertEqual(domains, {v: [False, True] for v in (X, Y, Z)})

    def test_no_global_assignment(self):
        self.assertFalse(k2.csp_satisfiable(k2.TRIANGLE_CSP, [X, Y, Z]))

    def test_each_edge_is_two_clauses(self):
        self.assertEqual(len(k2.TRIANGLE_CNF), 6)
        for (x, y, rel), clauses in zip(
            k2.TRIANGLE_CSP, zip(k2.TRIANGLE_CNF[0::2], k2.TRIANGLE_CNF[1::2])
        ):
            for a in (False, True):
                for b in (False, True):
                    self.assertEqual(
                        rel(a, b), k2.formula_satisfied(list(clauses), {x: a, y: b})
                    )

    def test_cnf_propagation_and_implication_graph(self):
        self.assertFalse(k2.brute_force_sat(k2.TRIANGLE_CNF))
        self.assertEqual(k2.unit_propagate(k2.TRIANGLE_CNF), ("fixpoint", {}))
        self.assertIsNotNone(
            k2.arc_consistency(k2.clausewise_csp(k2.TRIANGLE_CNF), [X, Y, Z])
        )
        self.assertEqual(
            k2.implication_path(k2.TRIANGLE_CNF, (X, False), (X, True)),
            [(X, False), (Y, True), (Z, False), (X, True)],
        )
        self.assertEqual(
            k2.implication_path(k2.TRIANGLE_CNF, (X, True), (X, False)),
            [(X, True), (Y, False), (Z, True), (X, False)],
        )
        self.assertFalse(k2.scc_2sat(k2.TRIANGLE_CNF))


class PairCleaningIsStronger(unittest.TestCase):
    """Kardash's operation checks joint tables of k+1 clause groups."""

    def test_issue_formulas_are_single_combination_instances(self):
        for formula in (k2.UP_COUNTEREXAMPLE, k2.TRIANGLE_CNF):
            tables = k2.pair_cleaning(formula)
            self.assertEqual(len(tables), 1)
            self.assertEqual(tables[0].rows, set())
            self.assertFalse(k2.pair_cleaning_nonempty(formula))

    def test_odd_disequality_cycles(self):
        for length in (5, 7):
            formula = k2.disequality_cycle_cnf(length)
            self.assertFalse(k2.brute_force_sat(formula))
            self.assertEqual(k2.unit_propagate(formula), ("fixpoint", {}))
            self.assertIsNotNone(
                k2.arc_consistency(k2.disequality_cycle(length), range(length))
            )
            self.assertFalse(k2.scc_2sat(formula))
            self.assertFalse(k2.pair_cleaning_nonempty(formula))


class AgreementWithBruteForce(unittest.TestCase):
    def check(self, formulas):
        counts = k2.summary(formulas)
        self.assertGreater(counts["unsat"], 0)
        # Neither incomplete procedure refutes any formula of binary clauses.
        self.assertEqual(counts["up_missed_unsat"], counts["unsat"])
        self.assertEqual(counts["ac_missed_unsat"], counts["unsat"])
        self.assertEqual(counts["scc_mismatch"], 0)
        self.assertEqual(counts["pair_cleaning_mismatch"], 0)
        return counts

    def test_every_2cnf_over_three_variables(self):
        counts = self.check(k2.exhaustive_formulas(3))
        self.assertEqual(counts["formulas"], 4095)

    def test_random_2cnf_over_four_to_six_variables(self):
        self.check(k2.random_formulas(587, 150, (4, 5, 6)))


FORBIDDEN_CLAIMS = [
    r"(?i)unit propagation\s+(?:on 2-SAT\s+)?IS complete",
    r"(?i)unit propagation on 2-SAT is equivalent to arc consistency",
    r"(?i)unit propagation[^.\n]*decides satisfiability",
    r"(?i)unit propagation \(a form of arc consistency\)",
    r"(?i)arc consistency\s+IS complete",
    r"(?i)where arc consistency is complete",
    r"(?i)Krom'?s 1967 theorem",
    r"(?i)pair cleaning(?: method)? is (?:exactly )?\**arc consistency",
    r"(?i)Only for k=2",
]


class SourceClaims(unittest.TestCase):
    def test_no_vacuous_2sat_axiom(self):
        for path in (LEAN, ROCQ):
            with self.subTest(path=path.name):
                source = path.read_text(encoding="utf-8")
                self.assertNotRegex(source, r"arcConsistency_complete")
                self.assertNotRegex(source, r"(?m)^\s*(?:axiom|Axiom)\s+\w+\s*:\s*True\b")

    def test_no_incorrect_completeness_explanation(self):
        for path in EXPLANATIONS:
            source = path.read_text(encoding="utf-8")
            for pattern in FORBIDDEN_CLAIMS:
                with self.subTest(path=str(path.relative_to(ROOT)), pattern=pattern):
                    self.assertNotRegex(source, pattern)

    def test_counterexamples_are_checked_in_lean(self):
        source = LEAN.read_text(encoding="utf-8")
        section = self.section(
            source, "section TwoSATCounterexamples", "end TwoSATCounterexamples"
        )
        self.assertNotRegex(section, r"\b(?:axiom|sorry|admit|native_decide)\b")
        for name in (
            "upCounterexample",
            "upCounterexample_unsat",
            "upCounterexample_unitPropagate_fixpoint",
            "upCounterexample_arcConsistent",
            "upCounterexample_implication_refutation",
            "triangleCSP",
            "triangle_arcConsistent",
            "triangle_unsat",
            "triangleCNF_encodes",
            "triangleCNF_unitPropagate_fixpoint",
            "triangleCNF_implication_refutation",
            "unitPropagate_2CNF_empty",
            "clausewiseCSP_arcConsistent",
            "contradictory_cycle_unsat",
        ):
            with self.subTest(name=name):
                self.assertRegex(section, rf"(?m)^(?:theorem|def) {name}\b")

    def test_counterexamples_are_checked_in_rocq(self):
        source = ROCQ.read_text(encoding="utf-8")
        section = self.section(
            source, "Section TwoSATCounterexamples.", "End TwoSATCounterexamples."
        )
        self.assertNotRegex(
            section, r"\b(?:Axiom|Parameter|Admitted|admit|Conjecture|Hypothesis)\b"
        )
        for name in (
            "upCounterexample",
            "upCounterexample_unsat",
            "upCounterexample_unitPropagate_fixpoint",
            "upCounterexample_arcConsistent",
            "upCounterexample_implication_refutation",
            "triangleCSP",
            "triangle_arcConsistent",
            "triangle_unsat",
            "triangleCNF_encodes",
            "triangleCNF_unitPropagate_fixpoint",
            "triangleCNF_implication_refutation",
            "unitPropagate_2CNF_empty",
            "clausewiseCSP_arcConsistent",
            "contradictory_cycle_unsat",
        ):
            with self.subTest(name=name):
                self.assertRegex(section, rf"(?m)^(?:Theorem|Lemma|Definition) {name}\b")

    def test_pair_cleaning_is_defined_before_completeness_claims(self):
        readme = (ATTEMPT / "refutation" / "README.md").read_text(encoding="utf-8")
        definition = readme.find("## What Pair Cleaning Computes")
        claim = readme.find("Pair cleaning for k = 2")
        self.assertGreaterEqual(definition, 0)
        self.assertGreater(claim, definition)
        self.assertIn("pairwise consistency", readme)
        self.assertIn("strongly connected component", readme)

    def test_workflow_runs_these_checks(self):
        workflow = WORKFLOW.read_text(encoding="utf-8")
        self.assertIn(
            "python3 -m unittest discover -s experiments/issue587 -p 'test_*.py' -v",
            workflow,
        )
        self.assertIn("bash experiments/issue587/check.sh --lean", workflow)
        self.assertIn("bash experiments/issue587/check.sh --rocq", workflow)

    @staticmethod
    def section(source, start, end):
        match = re.search(re.escape(start) + r"(.*?)" + re.escape(end), source, re.S)
        if match is None:
            raise AssertionError(f"missing {start!r} ... {end!r}")
        return match.group(1)


if __name__ == "__main__":
    unittest.main()
