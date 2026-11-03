#!/usr/bin/env python3
"""Issue #638: numeric check of the rank step in the upstream README's condensed hint.

This is NOT the identity of Anthropic's paper.  The paper (eth/paper.pdf at
16a5ce4, section 2.4, Lemma 2, Appendix F) is built on the eight-square
identity, eq. (12), which proofs/experiments/issue638/{lean/ETH.lean,
rocq/ETH.v} check at all 4096 settings (`eightSquare`).  The condensed hint
in anthropics/formal-math eth/README.md says:

    Put the nodes on a grid: the two diagonals of each rectangle form a swap.
    Per bit, SWAP = I - 2*singlet; grouping by the number of singlets gives
    lambda+1 operators with (row rank)*(column rank) <= 12^lambda.

This script checks that sentence under one explicit reading. It is evidence,
not a proof; the proof is Anthropic's Lean development, which the
`external-lean-reverification` workflow rebuilds.

Reading used here.  A rectangle has corners A=(i,j), B=(i,j'), C=(i',j),
D=(i',j').  Its diagonals A-D and B-C each carry lambda bits, so together they
form the tensor delta(a,d)*delta(b,c), i.e. the SWAP from (a,b) to (c,d).
* row rank    = rank of a tensor across the cut {A,B} | {C,D}
* column rank = rank of a tensor across the cut {A,C} | {B,D}
Per bit, with indices in {0,1}:
    SWAP[a,b,c,d]    = [a=d][b=c]
    I[a,b,c,d]       = [a=c][b=d]
    2*singlet[a,b,c,d] = eps[a,b]*eps[c,d], eps = [[0,1],[-1,0]]
so SWAP = I - 2*singlet.  For lambda bits, SWAP^{(x)lambda} = sum_j (-1)^j O_j
where O_j is the sum over all j-subsets T of the product with 2*singlet on T
and I elsewhere.

Ranks are computed exactly over Q, by fraction-free (Bareiss) elimination on
integer matrices, in pure Python.  Every Bareiss division is checked to be
exact.  As a cross-check, the ranks modulo two large primes are also computed;
they are lower bounds for the rank over Q and must not exceed it.

Usage: python3 -I experiments/issue638/swap_singlet_ranks.py [max_lambda]
"""
import itertools
import sys

PRIMES = (2_147_483_647, 1_000_000_007)


def eps(a, b):
    return (a == 0 and b == 1) - (a == 1 and b == 0)


def one_bit(kind, a, b, c, d):
    if kind == "I":
        return int(a == c and b == d)
    if kind == "S":  # 2 * singlet projector
        return eps(a, b) * eps(c, d)
    if kind == "SWAP":
        return int(a == d and b == c)
    raise ValueError(kind)


def check_one_bit_identity():
    for a, b, c, d in itertools.product((0, 1), repeat=4):
        lhs = one_bit("SWAP", a, b, c, d)
        rhs = one_bit("I", a, b, c, d) - one_bit("S", a, b, c, d)
        if lhs != rhs:
            return False
    return True


def tensor_entry(lam, j, a, b, c, d):
    """Entry of O_j at multi-indices a, b, c, d (tuples of lambda bits)."""
    total = 0
    for T in itertools.combinations(range(lam), j):
        prod = 1
        for i in range(lam):
            prod *= one_bit("S" if i in T else "I", a[i], b[i], c[i], d[i])
            if prod == 0:
                break
        total += prod
    return total


def rank_mod_p(rows, p):
    m = [[x % p for x in r] for r in rows]
    rank, ncols = 0, len(m[0]) if m else 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(m)) if m[r][col]), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        inv = pow(m[rank][col], p - 2, p)
        m[rank] = [(x * inv) % p for x in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][col]:
                f = m[r][col]
                m[r] = [(x - f * y) % p for x, y in zip(m[r], m[rank])]
        rank += 1
    return rank


def rank_exact(rows):
    """Rank over Q by fraction-free Gaussian elimination (Bareiss)."""
    m = [list(r) for r in rows]
    nrows, ncols = len(m), len(m[0]) if m else 0
    rank, prev = 0, 1
    for col in range(ncols):
        piv = next((r for r in range(rank, nrows) if m[r][col]), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        p = m[rank][col]
        for r in range(rank + 1, nrows):
            f = m[r][col]
            row = m[r]
            new = []
            for x, y in zip(row, m[rank]):
                num = p * x - f * y
                q, rem = divmod(num, prev)
                if rem:
                    raise ArithmeticError("Bareiss division not exact")
                new.append(q)
            m[r] = new
        prev = p
        rank += 1
    return rank


def ranks(lam, j):
    idx = list(itertools.product((0, 1), repeat=lam))
    cache = {}
    for a, b, c, d in itertools.product(idx, repeat=4):
        cache[(a, b, c, d)] = tensor_entry(lam, j, a, b, c, d)
    # row cut {A,B} | {C,D}
    row_mat = [[cache[(a, b, c, d)] for c in idx for d in idx] for a in idx for b in idx]
    # column cut {A,C} | {B,D}
    col_mat = [[cache[(a, b, c, d)] for b in idx for d in idx] for a in idx for c in idx]
    exact = (rank_exact(row_mat), rank_exact(col_mat))
    for p in PRIMES:
        mod = (rank_mod_p(row_mat, p), rank_mod_p(col_mat, p))
        if mod[0] > exact[0] or mod[1] > exact[1]:
            raise RuntimeError(f"rank mod {p} exceeds the rank over Q: {mod} > {exact}")
    return exact, cache


def main():
    max_lambda = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    ok = check_one_bit_identity()
    print(f"one-bit identity SWAP = I - 2*singlet: {'holds' if ok else 'FAILS'}")
    all_ok = ok
    for lam in range(1, max_lambda + 1):
        idx = list(itertools.product((0, 1), repeat=lam))
        swap_sum = {}
        worst = 0
        for j in range(lam + 1):
            (r, c), cache = ranks(lam, j)
            worst = max(worst, r * c)
            for key, val in cache.items():
                swap_sum[key] = swap_sum.get(key, 0) + (-1) ** j * val
            print(f"lambda={lam} j={j}: row rank over Q {r}, column rank over Q {c},"
                  f" product {r * c}"
                  f" (12^lambda = {12 ** lam})")
        expansion = all(
            swap_sum[(a, b, c, d)] == int(a == d and b == c)
            for a, b, c, d in itertools.product(idx, repeat=4)
        )
        bound = worst <= 12 ** lam
        all_ok &= expansion and bound
        print(f"lambda={lam}: sum_j (-1)^j O_j = SWAP: {'holds' if expansion else 'FAILS'};"
              f" max product {worst} <= 12^lambda: {'holds' if bound else 'FAILS'}")
    print("RESULT:", "all checks hold" if all_ok else "SOME CHECK FAILS")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
