"""Correctness checks for the educational DPLL solver."""

import itertools
import random
import unittest

from dpll_basic import Clause, DPLLSolver, Formula


def brute_force_satisfiable(formula):
    """Use truth-table enumeration as an independent SAT oracle."""
    for values in itertools.product((False, True), repeat=formula.num_vars):
        assignment = dict(enumerate(values, start=1))
        if satisfies(formula, assignment):
            return True
    return False


def satisfies(formula, assignment):
    """A returned partial model must already satisfy every original clause."""
    return all(
        any(assignment.get(abs(literal)) is (literal > 0)
            for literal in clause.literals)
        for clause in formula.clauses
    )


class DPLLCorrectnessTests(unittest.TestCase):
    def assert_agrees_with_brute_force(self, formula):
        expected = brute_force_satisfiable(formula)
        actual, assignment, _ = DPLLSolver().solve(formula)
        self.assertEqual(actual, expected, f"formula: {formula.clauses!r}")
        if actual:
            self.assertIsNotNone(assignment)
            self.assertTrue(satisfies(formula, assignment),
                            f"invalid model {assignment} for {formula.clauses!r}")
        else:
            self.assertIsNone(assignment)

    def test_issue_610_satisfiable_after_failed_unit_branch(self):
        formula = Formula([Clause(clause) for clause in (
            {-1, 2}, {-2, 3}, {-1, -3}, {1, -2}, {1, 3}
        )], num_vars=3)
        self.assert_agrees_with_brute_force(formula)

    def test_failed_branch_restores_all_unit_assignments(self):
        formula = Formula([Clause(clause) for clause in (
            {-1, 2}, {-2, 3}, {-1, -3}, {1, -2}, {1, 3}
        )], num_vars=3)
        assignment = {1: True}
        self.assertFalse(DPLLSolver()._dpll(formula, assignment, depth=1))
        self.assertEqual(assignment, {1: True})

    def test_failed_branch_restores_pure_assignment(self):
        # The first four clauses are an UNSAT core. x3 and x4 are pure.
        formula = Formula([Clause(clause) for clause in (
            {1, 2}, {1, -2}, {-1, 2}, {-1, -2}, {1, 3}, {1, 4}
        )], num_vars=4)
        assignment = {}
        solver = DPLLSolver()
        self.assertFalse(solver._dpll(formula, assignment, depth=0))
        self.assertGreaterEqual(solver.stats.num_pure_literals, 2)
        self.assertEqual(assignment, {})

    def test_exhaustive_small_formulas(self):
        for num_vars in (1, 2, 3):
            # Each variable is absent, positive, or negative in a clause.
            clauses = [frozenset(
                index * sign for index, sign in enumerate(signs, start=1)
                if sign
            ) for signs in itertools.product((0, -1, 1), repeat=num_vars)]
            max_clauses = len(clauses) if num_vars < 3 else 3
            for count in range(max_clauses + 1):
                for selected in itertools.combinations(clauses, count):
                    formula = Formula([Clause(set(clause)) for clause in selected],
                                      num_vars=num_vars)
                    self.assert_agrees_with_brute_force(formula)

    def test_seeded_random_larger_formulas(self):
        rng = random.Random(610)
        for num_vars in range(4, 8):
            for _ in range(100):
                clauses = []
                for _ in range(rng.randrange(1, 21)):
                    literals = set()
                    for _ in range(rng.randrange(0, 5)):
                        variable = rng.randrange(1, num_vars + 1)
                        literals.add(variable * rng.choice((-1, 1)))
                    clauses.append(Clause(literals))
                self.assert_agrees_with_brute_force(
                    Formula(clauses, num_vars=num_vars))


if __name__ == "__main__":
    unittest.main()
