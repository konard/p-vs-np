#!/usr/bin/env python3
"""Reference procedures for issue #587.

Literals use the convention of the Kardash refutation files: ``(i, neg)``
means ``x_i`` when ``neg`` is false and ``not x_i`` when ``neg`` is true.

The script compares four procedures on 2-CNF formulas with brute force:

* pure unit propagation from the empty assignment;
* arc consistency on the clause-by-clause binary CSP encoding;
* the implication-graph strongly connected component test
  (Aspvall, Plass, and Tarjan 1979);
* Kardash's pair cleaning method, implemented from Definitions 3-15 of
  ``proofs/attempts/sergey-kardash-2011-peqnp/original/ORIGINAL.md``.

Run it directly for a summary. The unit tests in ``test_kardash_2sat.py``
reuse these functions.
"""

from __future__ import annotations

import itertools
import random
import sys
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

Literal = Tuple[int, bool]
Clause = Tuple[Literal, ...]
Formula = Sequence[Clause]
Assignment = Dict[int, bool]


def lit(i: int, neg: bool = False) -> Literal:
    return (i, neg)


def literal_true(literal: Literal, value: bool) -> bool:
    return (not value) if literal[1] else value


def variables(formula: Formula) -> List[int]:
    return sorted({i for clause in formula for i, _ in clause})


def clause_satisfied(clause: Clause, assignment: Assignment) -> bool:
    return any(literal_true(l, assignment[l[0]]) for l in clause)


def formula_satisfied(formula: Formula, assignment: Assignment) -> bool:
    return all(clause_satisfied(clause, assignment) for clause in formula)


def brute_force_sat(formula: Formula) -> bool:
    vs = variables(formula)
    for values in itertools.product((False, True), repeat=len(vs)):
        if formula_satisfied(formula, dict(zip(vs, values))):
            return True
    return False


# ---------------------------------------------------------------------------
# Unit propagation
# ---------------------------------------------------------------------------

def unit_propagate(
    formula: Formula, assignment: Optional[Assignment] = None
) -> Tuple[str, Assignment]:
    """Return ``("conflict", rho)`` or ``("fixpoint", rho)``.

    No decisions are made: a literal is assigned only when a clause has all
    other literals false.
    """
    rho: Assignment = dict(assignment or {})
    while True:
        unit: Optional[Literal] = None
        for clause in formula:
            if any(l[0] in rho and literal_true(l, rho[l[0]]) for l in clause):
                continue
            open_lits = [l for l in clause if l[0] not in rho]
            if not open_lits:
                return "conflict", rho
            if len(open_lits) == 1 and unit is None:
                unit = open_lits[0]
        if unit is None:
            return "fixpoint", rho
        rho[unit[0]] = not unit[1]


# ---------------------------------------------------------------------------
# Binary CSP arc consistency
# ---------------------------------------------------------------------------

Relation = Callable[[bool, bool], bool]
Constraint = Tuple[int, int, Relation]


def clause_constraint(clause: Clause) -> Constraint:
    if len(clause) != 2 or clause[0][0] == clause[1][0]:
        raise ValueError(f"not a clause over two variables: {clause!r}")
    (x, nx), (y, ny) = clause
    return (
        x,
        y,
        lambda a, b, nx=nx, ny=ny: literal_true((x, nx), a)
        or literal_true((y, ny), b),
    )


def clausewise_csp(formula: Formula) -> List[Constraint]:
    """One binary constraint per clause; clauses on one scope are not merged."""
    return [clause_constraint(clause) for clause in formula]


def disequality_cycle(length: int) -> List[Constraint]:
    return [
        (i, (i + 1) % length, lambda a, b: a != b) for i in range(length)
    ]


def disequality_cycle_cnf(length: int) -> List[Clause]:
    clauses: List[Clause] = []
    for i in range(length):
        j = (i + 1) % length
        clauses.append((lit(i), lit(j)))
        clauses.append((lit(i, True), lit(j, True)))
    return clauses


def arc_consistency(
    csp: Sequence[Constraint], variables_: Iterable[int]
) -> Optional[Dict[int, List[bool]]]:
    """AC-3 from full Boolean domains; ``None`` means a domain wipe-out."""
    domains = {v: [False, True] for v in variables_}
    arcs = []
    for x, y, rel in csp:
        arcs.append((x, y, rel))
        arcs.append((y, x, lambda b, a, rel=rel: rel(a, b)))
    changed = True
    while changed:
        changed = False
        for x, y, rel in arcs:
            kept = [a for a in domains[x] if any(rel(a, b) for b in domains[y])]
            if len(kept) != len(domains[x]):
                domains[x] = kept
                changed = True
                if not kept:
                    return None
    return domains


def csp_satisfiable(csp: Sequence[Constraint], variables_: Sequence[int]) -> bool:
    for values in itertools.product((False, True), repeat=len(variables_)):
        a = dict(zip(variables_, values))
        if all(rel(a[x], a[y]) for x, y, rel in csp):
            return True
    return False


# ---------------------------------------------------------------------------
# Implication graph and strongly connected components
# ---------------------------------------------------------------------------

def negate(literal: Literal) -> Literal:
    return (literal[0], not literal[1])


def implication_edges(formula: Formula) -> List[Tuple[Literal, Literal]]:
    edges = []
    for clause in formula:
        if len(clause) != 2:
            raise ValueError(f"not a binary clause: {clause!r}")
        a, b = clause
        edges.append((negate(a), b))
        edges.append((negate(b), a))
    return edges


def reachable(formula: Formula, start: Literal) -> set:
    graph: Dict[Literal, List[Literal]] = {}
    for u, v in implication_edges(formula):
        graph.setdefault(u, []).append(v)
    seen = {start}
    stack = [start]
    while stack:
        u = stack.pop()
        for v in graph.get(u, []):
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def implication_path(
    formula: Formula, start: Literal, goal: Literal
) -> Optional[List[Literal]]:
    graph: Dict[Literal, List[Literal]] = {}
    for u, v in implication_edges(formula):
        graph.setdefault(u, []).append(v)
    parent: Dict[Literal, Optional[Literal]] = {start: None}
    queue = [start]
    for u in queue:
        if u == goal:
            path = [u]
            while parent[path[-1]] is not None:
                path.append(parent[path[-1]])  # type: ignore[arg-type]
            return list(reversed(path))
        for v in graph.get(u, []):
            if v not in parent:
                parent[v] = u
                queue.append(v)
    return None


def scc_2sat(formula: Formula) -> bool:
    """Aspvall-Plass-Tarjan: UNSAT iff some x and not x share an SCC."""
    nodes = sorted({l for i in variables(formula) for l in ((i, False), (i, True))})
    graph: Dict[Literal, List[Literal]] = {n: [] for n in nodes}
    for u, v in implication_edges(formula):
        graph[u].append(v)

    index: Dict[Literal, int] = {}
    low: Dict[Literal, int] = {}
    component: Dict[Literal, int] = {}
    stack: List[Literal] = []
    on_stack = set()
    counter = itertools.count()
    components = itertools.count()

    def strongconnect(v: Literal) -> None:
        index[v] = low[v] = next(counter)
        stack.append(v)
        on_stack.add(v)
        for w in graph[v]:
            if w not in index:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            c = next(components)
            while True:
                w = stack.pop()
                on_stack.discard(w)
                component[w] = c
                if w == v:
                    break

    for node in nodes:
        if node not in index:
            strongconnect(node)
    return all(component[(i, False)] != component[(i, True)] for i in variables(formula))


# ---------------------------------------------------------------------------
# Kardash pair cleaning (Definitions 3-15 of the original paper)
# ---------------------------------------------------------------------------

Row = Tuple[bool, ...]


class Table:
    """Value set of a clause combination: rows over ``scope``."""

    def __init__(self, scope: Tuple[int, ...], rows: Iterable[Row]):
        self.scope = scope
        self.rows = set(rows)

    def project(self, row: Row, onto: Sequence[int]) -> Row:
        position = {v: k for k, v in enumerate(self.scope)}
        return tuple(row[position[v]] for v in onto)


def clause_groups(formula: Formula) -> Dict[Tuple[int, ...], List[Clause]]:
    """Definition 3: clauses with the same variable index set form one group."""
    groups: Dict[Tuple[int, ...], List[Clause]] = {}
    for clause in formula:
        scope = tuple(sorted({i for i, _ in clause}))
        groups.setdefault(scope, []).append(clause)
    return groups


def combination_table(groups: Sequence[Tuple[Tuple[int, ...], List[Clause]]]) -> Table:
    """Definitions 5-8: all values of the combined variable set."""
    scope = tuple(sorted({v for group_scope, _ in groups for v in group_scope}))
    clauses = [clause for _, group in groups for clause in group]
    rows = []
    for values in itertools.product((False, True), repeat=len(scope)):
        if formula_satisfied(clauses, dict(zip(scope, values))):
            rows.append(values)
    return Table(scope, rows)


def relationship_structure(formula: Formula, k: int) -> List[Table]:
    """Definitions 9-10: value sets of all (k+1)-group clause combinations.

    When there are at most k+1 clause groups, the paper's Lemma 1 base case
    uses the single combination of every group.
    """
    groups = sorted(clause_groups(formula).items())
    if len(groups) <= k + 1:
        return [combination_table(groups)]
    return [combination_table(c) for c in itertools.combinations(groups, k + 1)]


def clear_pair(left: Table, right: Table) -> bool:
    """Definition 14. Returns whether a row was deleted."""
    common = tuple(v for v in left.scope if v in right.scope)
    left_keys = {left.project(r, common) for r in left.rows}
    right_keys = {right.project(r, common) for r in right.rows}
    new_left = {r for r in left.rows if left.project(r, common) in right_keys}
    new_right = {r for r in right.rows if right.project(r, common) in left_keys}
    changed = new_left != left.rows or new_right != right.rows
    left.rows, right.rows = new_left, new_right
    return changed


def pair_cleaning(formula: Formula, k: int = 2) -> List[Table]:
    """Definition 15: clear all pairs until no clearing changes a table."""
    tables = relationship_structure(formula, k)
    changed = True
    while changed:
        changed = False
        for i in range(len(tables)):
            for j in range(i + 1, len(tables)):
                changed |= clear_pair(tables[i], tables[j])
    return tables


def pair_cleaning_nonempty(formula: Formula, k: int = 2) -> bool:
    """Definition 12: the result is empty when any table is empty."""
    return all(table.rows for table in pair_cleaning(formula, k))


# ---------------------------------------------------------------------------
# Issue #587 examples and summary
# ---------------------------------------------------------------------------

X, Y, Z = 0, 1, 2

# (x or y) and (x or not y) and (not x or y) and (not x or not y)
UP_COUNTEREXAMPLE: List[Clause] = [
    (lit(X), lit(Y)),
    (lit(X), lit(Y, True)),
    (lit(X, True), lit(Y)),
    (lit(X, True), lit(Y, True)),
]

# x != y, y != z, z != x
TRIANGLE_CSP = disequality_cycle(3)
TRIANGLE_CNF = disequality_cycle_cnf(3)


def all_binary_clauses(n: int) -> List[Clause]:
    return [
        (lit(i, a), lit(j, b))
        for i, j in itertools.combinations(range(n), 2)
        for a in (False, True)
        for b in (False, True)
    ]


def exhaustive_formulas(n: int) -> Iterable[List[Clause]]:
    clauses = all_binary_clauses(n)
    for mask in range(1, 1 << len(clauses)):
        yield [c for bit, c in enumerate(clauses) if mask >> bit & 1]


def random_formulas(seed: int, count: int, sizes: Sequence[int]) -> Iterable[List[Clause]]:
    rng = random.Random(seed)
    for _ in range(count):
        n = rng.choice(sizes)
        clauses = all_binary_clauses(n)
        m = rng.randint(1, 2 * n + 2)
        yield rng.sample(clauses, min(m, len(clauses)))


def summary(formulas: Iterable[List[Clause]]) -> Dict[str, int]:
    counts = {
        "formulas": 0,
        "unsat": 0,
        "up_missed_unsat": 0,
        "ac_missed_unsat": 0,
        "scc_mismatch": 0,
        "pair_cleaning_mismatch": 0,
    }
    for formula in formulas:
        sat = brute_force_sat(formula)
        counts["formulas"] += 1
        counts["unsat"] += not sat
        if not sat and unit_propagate(formula)[0] == "fixpoint":
            counts["up_missed_unsat"] += 1
        if not sat and arc_consistency(clausewise_csp(formula), variables(formula)) is not None:
            counts["ac_missed_unsat"] += 1
        counts["scc_mismatch"] += scc_2sat(formula) != sat
        counts["pair_cleaning_mismatch"] += pair_cleaning_nonempty(formula) != sat
    return counts


def main() -> int:
    print("UP counterexample:")
    print("  unit propagation:", unit_propagate(UP_COUNTEREXAMPLE))
    print("  clause-wise AC:", arc_consistency(clausewise_csp(UP_COUNTEREXAMPLE), [X, Y]))
    print("  satisfiable:", brute_force_sat(UP_COUNTEREXAMPLE))
    print("  x -> not x:", implication_path(UP_COUNTEREXAMPLE, lit(X), lit(X, True)))
    print("  not x -> x:", implication_path(UP_COUNTEREXAMPLE, lit(X, True), lit(X)))
    print("  pair cleaning non-empty:", pair_cleaning_nonempty(UP_COUNTEREXAMPLE))
    print("Disequality triangle:")
    print("  AC domains:", arc_consistency(TRIANGLE_CSP, [X, Y, Z]))
    print("  CSP satisfiable:", csp_satisfiable(TRIANGLE_CSP, [X, Y, Z]))
    print("  CNF unit propagation:", unit_propagate(TRIANGLE_CNF))
    print("  x -> not x:", implication_path(TRIANGLE_CNF, lit(X), lit(X, True)))
    print("  not x -> x:", implication_path(TRIANGLE_CNF, lit(X, True), lit(X)))
    print("  pair cleaning non-empty:", pair_cleaning_nonempty(TRIANGLE_CNF))
    print("All 2-CNF formulas over 3 variables:", summary(exhaustive_formulas(3)))
    print("Random 2-CNF formulas over 4-6 variables:",
          summary(random_formulas(587, 300, (4, 5, 6))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
