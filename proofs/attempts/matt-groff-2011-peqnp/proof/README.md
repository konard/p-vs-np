# Forward Proof Formalization: Groff 2011

This directory contains the formal proof attempt following Groff's approach as faithfully as possible.

## Contents

- `lean/GroffProof.lean` - Lean 4 formalization
- `rocq/GroffProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **Clause Polynomial Construction**: Encoding each Boolean clause as a polynomial over a single variable x, where coefficients represent whether each truth assignment satisfies the clause.

2. **Polynomial Multiplication = Conjunction**: The claimed correspondence between arithmetic multiplication of modified clause polynomials and Boolean conjunction (AND).

3. **Hadamard Product Isolation**: The strategy of using multiplication and addition operations in a finite field to isolate the diagonal (satisfaction count) from off-diagonal terms.

4. **Finite Field Linear System**: The 2×2 linear system over GF(p) used to count how many truth assignments satisfy all clauses.

5. **Certificate Generation**: The iterative variable-fixing procedure for recovering a satisfying assignment.

6. **Polynomial Complexity Claim**: The assertion that all operations run in O(P · V(n+V)²) total time.

## The Attempted Proof Logic

Groff's argument proceeds:

1. **Encode Clauses**: For each clause in the k-SAT instance, construct a clause polynomial whose 2^V coefficients indicate which truth assignments satisfy the clause.

2. **Modify for Multiplication**: Transform coefficients from {0,1} to {1,a} (for a field element a ≠ 0,1) to enable algebraic manipulation.

3. **Eliminate Diagonal**: Choose constants a₀, a₁, c₀, c₁ in GF(p) such that combined multiplication/addition operations cancel the diagonal terms. This yields equations in unknowns b₀, b₁, b₂ (counts of 0, 1, 2 clauses satisfied).

4. **Reduce System**: Since b₀ + b₁ + b₂ = f(1) = 2^V, the system reduces to 2 equations in 2 unknowns.

5. **Solve**: Gaussian elimination in GF(p) gives b₂ = number of satisfying assignments to all n clauses.

6. **Decide**: If b₂ ≠ 0, output SAT. Otherwise output UNSAT (with small probability of error).

7. **Certify**: Fix variables one at a time and repeat to recover a satisfying assignment.

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Groff's argument fails. These mark locations where:

1. **Exponential Polynomial Size**: The clause polynomials have 2^V coefficients, so constructing and operating on them takes O(2^V) time — not polynomial. The formalizations cannot hide this exponential size.

2. **Single-Point Evaluation Loss**: Evaluating the polynomial at a single point x = c collapses 2^V coefficients to 1 number, losing all individual assignment information. The resulting "count" is an algebraic artifact, not the true count of satisfying assignments.

3. **Probabilistic Correctness**: The algorithm's correctness claim is probabilistic (error probability 1/Θ(V(n+V)²)^P). A proof of P = NP requires a deterministic, correct algorithm — not a probabilistic one (unless BPP = P, which is also unproven).

4. **Incomplete Original Proof**: Section 4 of the paper ends with "to be completed later..." indicating the walkthrough was never finished.

5. **Unproven Lemmas**: The correctness of the off-diagonal elimination (that the linear system truly counts satisfying assignments) relies on claims that the single-point polynomial evaluation faithfully tracks the clause structure — this is not proven.

## The Core Errors

**Error 1 (Exponential Size)**: The clause polynomial for a formula with V variables has 2^V coefficients. Every operation on this polynomial (evaluation, multiplication, addition) touches O(2^V) data, making the algorithm O(2^V) time.

**Error 2 (Information Loss)**: Evaluating at a single point x = c (mod p) gives one number, not a full truth table. The algorithm cannot distinguish which assignments are satisfying — only the (scrambled) sum of their contributions survives. This is not sufficient for a decision procedure without exponentially many evaluation points.

**Error 3 (Probabilistic Confusion)**: The algorithm can falsely classify a satisfiable formula as unsatisfiable. While the error probability is small, this makes it a probabilistic algorithm (BPP), not a deterministic polynomial-time algorithm (P). Proving P = NP requires P, not BPP (unless BPP = P, an open problem).

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Detailed refutation proof
