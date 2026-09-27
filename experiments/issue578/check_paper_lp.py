"""Finite check of a candidate witness for Gubin's systems (1.8) and (1.9).

Uses exact fractions and no external packages. This is an experiment, not a
formal proof; the Lean and Rocq certificates must independently check it.
"""

from fractions import Fraction
from itertools import permutations, product

N = 6
EDGE = {(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)}


def other_component(mu, nu):
    return (mu < 3) != (nu < 3)


def y(j, nu):
    return Fraction(1, 6)


def x(i, j, mu, nu):
    if i == j or mu == nu:
        return Fraction(0)
    if (i + 1) % N == j:
        return Fraction(1, 6) if (mu, nu) in EDGE else Fraction(0)
    if (j + 1) % N == i:
        return Fraction(1, 6) if (nu, mu) in EDGE else Fraction(0)
    return Fraction(1, 18) if other_component(mu, nu) else Fraction(0)


def compatible(i, j, mu, nu):
    return (
        (i + 1) % N != j or (mu, nu) in EDGE
    ) and ((j + 1) % N != i or (nu, mu) in EDGE)


def main():
    for i, j, mu, nu in product(range(N), repeat=4):
        if i != j and mu != nu:
            assert x(i, j, mu, nu) >= 0
            assert x(i, j, mu, nu) == x(j, i, nu, mu)
            if not compatible(i, j, mu, nu):
                assert x(i, j, mu, nu) == 0
    for i, j, nu in product(range(N), repeat=3):
        if i != j:
            assert sum(x(i, j, mu, nu) for mu in range(N) if mu != nu) == y(j, nu)
    for j, mu, nu in product(range(N), repeat=3):
        if mu != nu:
            assert sum(x(i, j, mu, nu) for i in range(N) if i != j) == y(j, nu)
    for j in range(N):
        assert sum(y(j, nu) for nu in range(N)) == 1
        assert all(y(j, nu) >= 0 for nu in range(N))
    tours = [p for p in permutations(range(N)) if all((p[i], p[(i + 1) % N]) in EDGE for i in range(N))]
    assert not tours
    print("Six-vertex instance satisfies (1.8) and (1.9) but has no Hamiltonian tour")


if __name__ == "__main__":
    main()
