# Refutation — Bangyan Wen & Yi Lin (2010)

## The Core Error

The paper commits a fundamental logical fallacy:

> **Wen & Lin's error**: The observation that the certificate search space for NP problems
> is exponentially large does **not** imply that no polynomial-time algorithm can decide
> NP problems. A polynomial-time algorithm for an NP problem would not enumerate all
> certificates — it would use the structure of the specific problem to find an answer
> directly in polynomial time.

## What We Prove

### 1. The Logical Gap: Exponential Search Space ≠ Exponential Decision Time

The paper's argument is:
```
(1) NP certificate search space is exponential
(2) Naive enumeration takes exponential time
(3) Therefore no polynomial-time algorithm exists  ← UNJUSTIFIED
```

Step (3) does not follow from (1) and (2). Many problems have exponentially large
spaces of potential solutions but are nevertheless solvable in polynomial time by
algorithms that exploit problem structure. Examples:

- **Shortest Path**: Exponentially many paths between two nodes, yet solvable in O(V·E).
- **Linear Programming**: Exponentially many basic feasible solutions, yet solvable in poly time (ellipsoid method).
- **Maximum Matching**: Exponentially many subsets of edges to check, yet solvable in poly time.

The paper provides no argument for why NP-complete problems cannot have similar structural properties.

### 2. The Relativization Barrier

A proof technique that works purely from formal logical definitions of P and NP
necessarily "relativizes" — it works equally well when we add an oracle to both P
and NP. But Baker-Gill-Solovay (1975) showed:

- There exists oracle A such that P^A = NP^A
- There exists oracle B such that P^B ≠ NP^B

Therefore, any proof of P ≠ NP based only on formal logic definitions cannot be correct,
because such a proof would also work relative to oracle A, giving a contradiction.

### 3. The Quantifier Asymmetry Is Not Enough

The paper observes that NP uses an existential quantifier (∃ certificate) while P uses
bounded deterministic computation. This is correct as a characterization, but:

- P can also be described with bounded existential quantifiers (via witness-based certificates — in fact P ⊆ NP precisely because every P problem also has polynomial verifiers).
- The *question* of P vs NP is whether the existential quantifier in NP adds power beyond deterministic polynomial computation.
- Observing the asymmetry is not the same as proving it matters computationally.

### 4. What Would Be Required for a Valid Proof

A valid proof of P ≠ NP would need one of:
- **Circuit lower bounds**: Show that some specific NP problem (e.g., SAT) requires super-polynomial Boolean circuit size.
- **Non-relativizing diagonalization**: A diagonalization argument that explicitly exploits non-oracle-accessible structure.
- **New mathematical framework**: A technique that overcomes relativization, natural proofs, and algebrization barriers simultaneously.

The paper's formal logic approach provides none of these.

## Formal Refutation

The Lean and Rocq files formalize:

1. `exponential_space_not_sufficient` — Having an exponential search space does not
   imply exponential decision time (shown via counterexamples).

2. `relativization_barrier` — Any argument based solely on the formal definitions
   of P and NP relativizes and thus cannot separate the classes.

3. `quantifier_asymmetry_insufficient` — The ∃ vs. deterministic-computation asymmetry
   is the P vs NP question itself, not a proof of it.

4. `wen_lin_inference_invalid` — The main inference step in the paper is explicitly
   marked as not provable from the given premises.

## Files

- `lean/WenLinRefutation.lean` — Lean 4 formalization of the refutation
- `rocq/WenLinRefutation.v` — Rocq (Coq) formalization of the refutation
