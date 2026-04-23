# Forward Proof Formalization: Kardash 2011

This directory contains the formal proof attempt following Kardash's approach as faithfully as possible.

## Contents

- `lean/KardashProof.lean` — Lean 4 formalization
- `rocq/KardashProof.v` — Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **Clause Groups**: Sets of clauses sharing the same k variable indices; their value tables
2. **Clause Combinations**: Sets of (k+1) clause groups; their joint value tables
3. **Relationship Structure**: The set of all C(nt, k+1) clause combinations
4. **Pair Cleaning**: Iterative pairwise removal of inconsistent rows across clause combinations
5. **The Claimed Theorem**: Non-empty result after cleaning ⟺ formula is satisfiable
6. **Complexity**: O(n^{3(k+1)}) claimed runtime

## The Attempted Proof Logic

Kardash's argument proceeds:

1. **Clause Group Abstraction**: Group clauses by their variable index sets; compute satisfying assignments for each group
2. **Relationship Structure**: Enumerate all (k+1)-subsets of clause groups as clause combinations
3. **Pair Cleaning**: Remove assignments from each clause combination's table that cannot be extended consistently to any row in an overlapping clause combination
4. **Lemma 1**: After cleaning, non-empty result ⟺ there exists a single-valued unclearable structure (proved by induction on nt)
5. **Lemma 2**: Single-valued unclearable structure ⟺ satisfying assignment
6. **Theorem 1**: Combine Lemmas 1 and 2
7. **Complexity**: O(nt^{3(k+1)}) = O(n^{3(k+1)}) since nt ≤ n

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gap where Kardash's argument fails:

**The inductive step of Lemma 1**: The claim that any non-empty cleaned structure contains a single-valued unclearable sub-structure. The proof assumes that local pairwise consistency implies global consistency, which is false in general.

Specifically: when extending from Bnt(x) to Ant+1(x) by adding clause group Tnt+1, the proof asserts that the single-valued structure from the induction hypothesis can always be extended consistently. This requires that arc consistency implies satisfiability — which it does not for k ≥ 3.

## See Also

- [`../README.md`](../README.md) — Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) — Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) — Explanation of why the proof fails
