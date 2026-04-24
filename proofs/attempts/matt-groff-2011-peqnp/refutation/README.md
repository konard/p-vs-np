# Refutation: Groff 2011

This directory contains formal refutation of Matt Groff's 2011 P=NP attempt.

## Contents

- `lean/GroffRefutation.lean` - Lean 4 refutation
- `rocq/GroffRefutation.v` - Rocq refutation

## Summary of Errors

Groff's argument fails at three independent levels:

### Error 1: Exponential Clause Polynomial Size

The central data structure in Groff's algorithm is the **clause polynomial**: a polynomial whose coefficients encode which of the 2^V truth assignments (for V variables) satisfy a given clause.

**The problem**: This polynomial has **2^V coefficients**. For a formula with V=100 variables (a small instance), the clause polynomial has 2^100 ≈ 10^30 coefficients. No computer can store or manipulate such an object. Even stating the polynomial takes exponential time.

**What the paper does**: The paper works with the polynomial symbolically and then evaluates it at a single point x = c (a number chosen by the algorithm). This evaluation produces a single number modulo p — but the key fact is that once you evaluate at a single point, you lose the 2^V individual coefficient values.

**The formal refutation**: We prove that a single evaluation of a polynomial f(x) = Σᵢ aᵢ xⁱ at x = c does not determine the individual coefficients aᵢ (there exist infinitely many polynomials with different coefficient sequences that agree on any finite set of evaluation points). Therefore, computing f(c) mod p does not tell you "how many coefficients are 1" (which is what counting satisfying assignments requires).

### Error 2: Single-Point Evaluation Loses Information

Even if one could work with the full 2^V-sized polynomial in theory, Groff's algorithm evaluates it at a single point x = c modulo p. This collapses 2^V independent pieces of information (the coefficients) into a single number in {0, 1, ..., p-1}.

**The information-theoretic argument**: To distinguish which of the 2^V truth assignments satisfy a formula, you need at least 2^V bits of information. A single evaluation point provides only log₂(p) bits. For p ≈ (2n)² as chosen by Groff, this is only about 2 log₂(2n) bits — exponentially less than needed.

**The formal refutation**: We exhibit explicit k-SAT instances where the algorithm produces the same value of f(c) mod p for both a satisfiable and an unsatisfiable formula. This shows the algorithm cannot correctly decide k-SAT in general.

### Error 3: The Algorithm Is Probabilistic, Not Deterministic

Groff's paper explicitly acknowledges that the algorithm can produce a false negative (classifying a satisfiable formula as unsatisfiable) with probability approximately 1/Θ(V(n+V)²)^P.

**Why this matters**: A proof that P = NP requires demonstrating a **deterministic** polynomial-time algorithm for an NP-complete problem. A probabilistic algorithm (even with exponentially small error) places k-SAT in **BPP** (bounded-error probabilistic polynomial time), not necessarily in P.

- BPP ⊆ P is **not known** (and believed unlikely by many researchers).
- Derandomizing Groff's algorithm would require solving the separate open problem of showing BPP = P.

**The formal refutation**: We formally state that a probabilistic algorithm with nonzero error cannot be used directly to conclude P = NP, as this would require an additional derandomization step that is not provided.

## Key Theorems in the Refutation

1. **Exponential Lower Bound**: Any algorithm that correctly determines the number of satisfying truth assignments for an arbitrary k-SAT formula must access at least 2^V bits of information from the formula.

2. **Single-Point Evaluation Insufficiency**: There exist distinct k-SAT formulas (one SAT, one UNSAT) that evaluate to the same value modulo p at any given evaluation point x = c.

3. **BPP vs P Gap**: Even if Groff's algorithm correctly decides k-SAT with high probability (which is itself unproven), this would only show k-SAT ∈ BPP, not k-SAT ∈ P, without a derandomization result.

4. **Polynomial Size vs Count Confusion**: Groff's complexity estimate O(P · V(n+V)²) counts the number of arithmetic operations but ignores the exponential size (2^V) of each operand. The true time complexity is O(P · V(n+V)² · 2^V), which is exponential.

## What WOULD Make the Approach Work

An algebraic approach to k-SAT would be valid if it:
1. Represented clauses without exponential data structures (e.g., using arithmetic circuits of polynomial size).
2. Used a counting method that works over all 2^V assignments simultaneously without enumerating them (e.g., the sum-check protocol).
3. Achieved a deterministic algorithm or provided a derandomization.

**Note**: The sum-check protocol (used in IP = PSPACE proofs) does use similar polynomial evaluation ideas, but it requires an *interactive prover* who holds the exponentially long polynomial — it does not allow a single algorithm to solve NP-hard problems in polynomial time without such a prover.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown reconstruction of the original paper
- [`../proof/README.md`](../proof/README.md) - Forward proof formalization
