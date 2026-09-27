"""Enumerate a small degree-two, strongly connected projector example."""

from itertools import product


def edge(u, v):
    return v // 2 == (u // 2 + 1) % 3


def matching(bits):
    return tuple(2 * ((u // 2 + 1) % 3) + (u % 2 ^ bits[u // 2]) for u in range(6))


def rank_of_incidence(permutation):
    # For a functional digraph, incidence rank is n minus the cycle count.
    unseen = set(range(6))
    cycles = 0
    while unseen:
        cycles += 1
        u = next(iter(unseen))
        while u in unseen:
            unseen.remove(u)
            u = permutation[u]
    return 6 - cycles


def reachable_from(start):
    seen = {start}
    while True:
        next_seen = seen | {v for u in seen for v in range(6) if edge(u, v)}
        if next_seen == seen:
            return seen
        seen = next_seen


if __name__ == "__main__":
    assert all(reachable_from(u) == set(range(6)) for u in range(6))
    rows = []
    for bits in product(range(2), repeat=3):
        m = matching(bits)
        assert len(set(m)) == 6
        assert all(edge(u, m[u]) for u in range(6))
        rows.append((bits, m, rank_of_incidence(m)))
    assert len({row[1] for row in rows}) == 8
    for row in rows:
        print(row)
