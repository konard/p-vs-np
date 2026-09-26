"""Search small digraphs for feasibility of Gubin's (1.8)-(1.9) without tours.

Requires highspy. The LP uses the indices and equations printed in the arXiv
version, cs/0610042v3, pages 4-6. A candidate still needs exact certification.
"""

from itertools import permutations, product
import random
import sys

import highspy


def has_tour(n, edges):
    return any(
        all((p[i], p[(i + 1) % n]) in edges for i in range(n))
        for p in permutations(range(n))
    )


def solve(n, edges):
    h = highspy.Highs()
    h.silent()
    x = {
        (i, j, mu, nu): h.addVariable(lb=0, ub=0 if
            ((i + 1) % n == j and (mu, nu) not in edges) or
            ((j + 1) % n == i and (nu, mu) not in edges) else highspy.kHighsInf)
        for i, j, mu, nu in product(range(n), repeat=4)
        if i != j and mu != nu
    }
    y = {(j, nu): h.addVariable(lb=0) for j, nu in product(range(n), repeat=2)}
    for i, j, mu, nu in x:
        if i < j:
            h.addConstr(x[i, j, mu, nu] == x[j, i, nu, mu])
    for i, j, nu in product(range(n), repeat=3):
        if i != j:
            h.addConstr(sum(x[i, j, mu, nu] for mu in range(n) if mu != nu) == y[j, nu])
    for j, mu, nu in product(range(n), repeat=3):
        if mu != nu:
            h.addConstr(sum(x[i, j, mu, nu] for i in range(n) if i != j) == y[j, nu])
    for j in range(n):
        h.addConstr(sum(y[j, nu] for nu in range(n)) == 1)
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    return {key: h.val(var) for key, var in x.items()}, {key: h.val(var) for key, var in y.items()}


def main():
    random.seed(578)
    for n in (4, 5, 6):
        all_edges = [(i, j) for i in range(n) for j in range(n) if i != j]
        for trial in range(1000):
            p = random.uniform(0.3, 0.8)
            edges = {edge for edge in all_edges if random.random() < p}
            if has_tour(n, edges):
                continue
            result = solve(n, edges)
            if result is not None:
                x, y = result
                print(f"n={n}, trial={trial}, p={p}, edges={sorted(edges)}", flush=True)
                print(f"nonzero y={sum(abs(v) > 1e-8 for v in y.values())}", flush=True)
                print(f"nonzero x={sum(abs(v) > 1e-8 for v in x.values())}", flush=True)
                return 0
        print(f"no witness for n={n} in 1000 trials", file=sys.stderr, flush=True)
    return 1


if __name__ == "__main__":
    sys.exit(main())
