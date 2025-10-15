#!/usr/bin/env python3
"""
Basic DPLL SAT Solver Implementation

Purpose: Educational implementation to demonstrate why SAT is hard.
This implements the classic DPLL algorithm with unit propagation and
pure literal elimination.

Expected behavior: Exponential time in worst case (demonstrates the hardness).

References:
- Davis, Putnam (1960): "A Computing Procedure for Quantification Theory"
- Davis, Logemann, Loveland (1962): "A Machine Program for Theorem-Proving"
"""

from typing import Set, Dict, List, Tuple, Optional
from dataclasses import dataclass
import time


@dataclass
class Clause:
    """A clause is a disjunction of literals (variables or their negations)"""
    literals: Set[int]  # Positive int = variable, negative = negation

    def __repr__(self):
        return " ∨ ".join(f"{'¬' if lit < 0 else ''}x{abs(lit)}" for lit in sorted(self.literals, key=abs))


@dataclass
class Formula:
    """A CNF formula is a conjunction of clauses"""
    clauses: List[Clause]
    num_vars: int

    def __repr__(self):
        return " ∧ ".join(f"({c})" for c in self.clauses)


@dataclass
class SolverStats:
    """Statistics about the solving process"""
    num_decisions: int = 0  # Number of branching decisions
    num_unit_props: int = 0  # Number of unit propagations
    num_pure_literals: int = 0  # Number of pure literal eliminations
    max_depth: int = 0  # Maximum recursion depth reached

    def report(self) -> str:
        return (f"Decisions: {self.num_decisions}, "
                f"Unit propagations: {self.num_unit_props}, "
                f"Pure literals: {self.num_pure_literals}, "
                f"Max depth: {self.max_depth}")


class DPLLSolver:
    """
    DPLL SAT Solver

    Demonstrates the exponential worst-case behavior that makes SAT hard.
    """

    def __init__(self):
        self.stats = SolverStats()

    def solve(self, formula: Formula) -> Tuple[bool, Optional[Dict[int, bool]], SolverStats]:
        """
        Solve SAT instance using DPLL algorithm.

        Returns:
            (satisfiable, assignment, stats)
            - satisfiable: True if formula is SAT, False if UNSAT
            - assignment: Dictionary mapping variables to True/False (if SAT)
            - stats: Statistics about the solving process
        """
        self.stats = SolverStats()
        assignment: Dict[int, bool] = {}

        result = self._dpll(formula, assignment, depth=0)

        return result, assignment if result else None, self.stats

    def _dpll(self, formula: Formula, assignment: Dict[int, bool], depth: int) -> bool:
        """
        Recursive DPLL procedure.

        Returns True if satisfiable, False otherwise.
        Modifies assignment in place.
        """
        # Update statistics
        self.stats.max_depth = max(self.stats.max_depth, depth)

        # Simplify formula under current assignment
        simplified = self._simplify(formula, assignment)

        # Base case 1: All clauses satisfied
        if not simplified.clauses:
            return True

        # Base case 2: Empty clause (conflict)
        if any(len(c.literals) == 0 for c in simplified.clauses):
            return False

        # Unit propagation: Find unit clauses (single literal)
        while True:
            unit_clause = self._find_unit_clause(simplified)
            if unit_clause is None:
                break

            # Extract the literal
            literal = next(iter(unit_clause.literals))
            var = abs(literal)
            value = literal > 0

            # Assign the variable
            assignment[var] = value
            self.stats.num_unit_props += 1

            # Simplify with new assignment
            simplified = self._simplify(simplified, assignment)

            # Check for conflict
            if any(len(c.literals) == 0 for c in simplified.clauses):
                del assignment[var]  # Backtrack
                return False

        # Check if solved after unit propagation
        if not simplified.clauses:
            return True

        # Pure literal elimination
        pure_literal = self._find_pure_literal(simplified)
        if pure_literal is not None:
            var = abs(pure_literal)
            value = pure_literal > 0
            assignment[var] = value
            self.stats.num_pure_literals += 1

            # Recursively solve simplified formula
            return self._dpll(formula, assignment, depth + 1)

        # Branching: Choose a variable to assign
        # (This is where exponential blowup occurs)
        self.stats.num_decisions += 1
        var = self._choose_variable(simplified)

        # Try assigning variable to True
        assignment[var] = True
        if self._dpll(formula, assignment, depth + 1):
            return True

        # Backtrack and try False
        assignment[var] = False
        if self._dpll(formula, assignment, depth + 1):
            return True

        # Both branches failed, backtrack
        del assignment[var]
        return False

    def _simplify(self, formula: Formula, assignment: Dict[int, bool]) -> Formula:
        """
        Simplify formula under current partial assignment.

        - Remove clauses that are satisfied
        - Remove literals that are false from remaining clauses
        """
        new_clauses = []

        for clause in formula.clauses:
            # Check if clause is satisfied
            satisfied = False
            new_literals = set()

            for lit in clause.literals:
                var = abs(lit)
                if var in assignment:
                    # Variable is assigned
                    value = assignment[var]
                    if (lit > 0 and value) or (lit < 0 and not value):
                        # Literal is true, clause is satisfied
                        satisfied = True
                        break
                    # else: Literal is false, don't include it
                else:
                    # Variable not yet assigned
                    new_literals.add(lit)

            if not satisfied:
                new_clauses.append(Clause(new_literals))

        return Formula(new_clauses, formula.num_vars)

    def _find_unit_clause(self, formula: Formula) -> Optional[Clause]:
        """Find a clause with exactly one literal (unit clause)"""
        for clause in formula.clauses:
            if len(clause.literals) == 1:
                return clause
        return None

    def _find_pure_literal(self, formula: Formula) -> Optional[int]:
        """
        Find a variable that appears only positively or only negatively.
        """
        positive_vars = set()
        negative_vars = set()

        for clause in formula.clauses:
            for lit in clause.literals:
                if lit > 0:
                    positive_vars.add(lit)
                else:
                    negative_vars.add(-lit)

        # Find variables that appear only positively
        pure_positive = positive_vars - negative_vars
        if pure_positive:
            return min(pure_positive)

        # Find variables that appear only negatively
        pure_negative = negative_vars - positive_vars
        if pure_negative:
            return -min(pure_negative)

        return None

    def _choose_variable(self, formula: Formula) -> int:
        """
        Choose next variable to branch on.

        Simple heuristic: Choose variable appearing in most clauses.
        Better heuristics (VSIDS, etc.) exist but add complexity.
        """
        var_count: Dict[int, int] = {}

        for clause in formula.clauses:
            for lit in clause.literals:
                var = abs(lit)
                var_count[var] = var_count.get(var, 0) + 1

        return max(var_count.items(), key=lambda x: x[1])[0]


def create_example_formulas() -> List[Tuple[str, Formula]]:
    """Create example formulas to demonstrate solver behavior"""

    examples = []

    # Example 1: Simple satisfiable formula
    # (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3)
    # Satisfiable: x1=True, x2=False, x3=True
    examples.append(("Simple SAT", Formula([
        Clause({1, 2}),
        Clause({-1, 3}),
        Clause({-2, -3})
    ], num_vars=3)))

    # Example 2: Simple unsatisfiable formula
    # (x1) ∧ (¬x1)
    examples.append(("Simple UNSAT", Formula([
        Clause({1}),
        Clause({-1})
    ], num_vars=1)))

    # Example 3: Pigeonhole principle (n+1 pigeons, n holes)
    # This is UNSAT and requires exponential time for DPLL
    # For 3 pigeons, 2 holes:
    # Each pigeon must be in some hole: (p1h1 ∨ p1h2) ∧ (p2h1 ∨ p2h2) ∧ (p3h1 ∨ p3h2)
    # No two pigeons in same hole: (¬p1h1 ∨ ¬p2h1) ∧ (¬p1h1 ∨ ¬p3h1) ∧ (¬p2h1 ∨ ¬p3h1)
    #                               (¬p1h2 ∨ ¬p2h2) ∧ (¬p1h2 ∨ ¬p3h2) ∧ (¬p2h2 ∨ ¬p3h2)
    # Variable encoding: pigeon i in hole j = variable (i-1)*2 + j
    clauses = []
    pigeons, holes = 3, 2

    # Each pigeon in some hole
    for p in range(1, pigeons + 1):
        clause_lits = {(p-1)*holes + h for h in range(1, holes + 1)}
        clauses.append(Clause(clause_lits))

    # No two pigeons in same hole
    for h in range(1, holes + 1):
        for p1 in range(1, pigeons + 1):
            for p2 in range(p1 + 1, pigeons + 1):
                var1 = (p1-1)*holes + h
                var2 = (p2-1)*holes + h
                clauses.append(Clause({-var1, -var2}))

    examples.append(("Pigeonhole (3,2) [HARD UNSAT]", Formula(
        clauses, num_vars=pigeons*holes
    )))

    return examples


def main():
    """Demonstrate DPLL solver on example formulas"""
    print("=" * 70)
    print("DPLL SAT Solver - Educational Demonstration")
    print("=" * 70)
    print()
    print("Purpose: Show why SAT is hard (exponential worst-case behavior)")
    print()

    examples = create_example_formulas()
    solver = DPLLSolver()

    for name, formula in examples:
        print(f"Example: {name}")
        print(f"Formula: {formula}")
        print(f"Variables: {formula.num_vars}, Clauses: {len(formula.clauses)}")
        print()

        start_time = time.time()
        satisfiable, assignment, stats = solver.solve(formula)
        elapsed = time.time() - start_time

        print(f"Result: {'SATISFIABLE' if satisfiable else 'UNSATISFIABLE'}")
        if satisfiable and assignment:
            print(f"Assignment: {assignment}")
        print(f"Time: {elapsed*1000:.2f} ms")
        print(f"Stats: {stats.report()}")
        print()
        print("-" * 70)
        print()

    print("Key Observations:")
    print("1. Simple formulas solved quickly")
    print("2. Pigeonhole principle requires exponential branching")
    print("3. Number of decisions grows exponentially with problem size")
    print("4. This demonstrates why SAT is hard!")
    print()
    print("For P = NP to be true, we would need a fundamentally different")
    print("algorithm that avoids this exponential explosion.")
    print("=" * 70)


if __name__ == "__main__":
    main()
