# Matt Groff (2011) - P=NP via k-SAT Using Linear Algebra on Finite Fields

**Attempt ID**: 75 (from Woeginger's list)
**Author**: Matt Groff
**Year**: 2011 (submitted June 3, 2011; revised October 1, 2011)
**Claim**: P = NP
**Status**: Refuted

## Summary

In June 2011, Matt Groff submitted a paper to arXiv titled "Towards P = NP via k-SAT: A k-SAT Algorithm Using Linear Algebra on Finite Fields." The paper presents a novel approach to solving the k-SAT problem using linear algebra over finite fields. The author encodes Boolean clauses as polynomials, then uses multiplication and addition of these polynomials (along with modular arithmetic over prime finite fields) to determine whether a given Boolean formula can be satisfied. The paper concludes that "significant evidence exists that P=NP."

The paper is notable for its accessibility — it is written to be understood by people from many diverse fields — and for the fact that the author acknowledges it is a "semi-complete first draft." The paper includes source code on SourceForge for independent verification.

## Main Argument

### The Approach

The algorithm proceeds in several key stages:

1. **Clause Polynomials**: Each clause in the k-SAT instance is encoded as a polynomial over a single variable `x`. The coefficients of this polynomial represent whether each truth assignment satisfies the clause (coefficient 1) or not (coefficient 0).

2. **Polynomial Multiplication = Conjunction**: Multiplying two clause polynomials over modified coefficients corresponds to computing their conjunction (AND). The algorithm exploits the fact that Boolean AND and arithmetic multiplication agree on bit values (0 and 1).

3. **Finite Field Arithmetic**: Operations are performed modulo a chosen prime `p`, where `p` is chosen to be larger than `(2n)²` (with `n` = number of clauses). This bounds the error probability.

4. **Hadamard Product Isolation**: The algorithm aims to isolate the "diagonal" of the polynomial multiplication matrix, which represents the number of satisfying assignments. This uses a combination of multiplication and addition operations in the finite field.

5. **Off-diagonal Elimination**: By choosing appropriate constants `a₀, a₁, ...` (distinct field elements) and scalars `c₀, c₁, ...`, the algorithm sets up a linear system of equations in three unknowns (`b₀`, `b₁`, `b₂`), representing the count of 0, 1, or 2 clauses satisfied. One unknown is dependent (the three counts sum to `f(1)`, the "function of ones"), reducing to a 2×2 linear system.

6. **Decision**: If the number of fully-satisfying assignments (all `n` clauses satisfied) is nonzero, the formula is satisfiable. Otherwise, there is at most a `1/Θ(V(n+V)²)^P` probability of a false negative.

7. **Certificate Generation**: To obtain a satisfying assignment, the algorithm iterates: fix the first variable to `true`, check satisfiability of the reduced formula, then fix the next variable, etc. This runs the basic algorithm `O(V)` additional times.

### Stated Complexity

- The 2-clause algorithm is applied repeatedly in a tree structure with `O(V)(n+V)²` total iterations.
- Using `P` independent primes to reduce error gives total runtime **O(P · V(n+V)²)**, claimed to be polynomial.
- Error probability: approximately `1/Θ(V(n+V)²)^P`.

### Key Technical Claims

1. The clause polynomial construction correctly encodes which truth assignments satisfy each clause.
2. Polynomial multiplication over modified coefficients correctly isolates conjunction results.
3. The off-diagonal elimination via finite-field linear algebra yields correct counts of satisfying assignments.
4. The linear system is solvable in polynomial time (it reduces to 2×2).
5. The overall algorithm runs in polynomial time, implying k-SAT ∈ P, hence P = NP.

## The Errors

### Error 1: The Algorithm Is Probabilistic, Not Deterministic

The algorithm has an inherent probabilistic error: it can mistakenly classify a satisfiable formula as unsatisfiable with probability approximately `1/Θ(V(n+V)²)^P`. This means the algorithm is a **probabilistic algorithm** (in the class BPP), not a deterministic polynomial-time algorithm (in P).

- If P = NP were proved this way, one would need to derandomize this algorithm — which is an open problem.
- The paper itself acknowledges "evidence" rather than a proof, and explicitly states only that the satisfiability number is non-zero with high probability.

### Error 2: The Polynomial Size is Exponential

The clause polynomials encode all `2^V` possible truth assignments of `V` variables, so each clause polynomial has **2^V coefficients**. For a k-SAT instance with `V` variables:

- Constructing a single clause polynomial takes `O(2^V)` time and space.
- All subsequent operations (multiplication, addition, linear algebra) are performed on these `2^V`-sized objects.

Even if the number of arithmetic operations is polynomial in `n` and `V`, each operation works on exponentially large polynomials. The total complexity is therefore **exponential** in `V`, not polynomial.

The paper obscures this by working with the polynomial symbolically and by evaluating the polynomial at a single point `x = some value`. However, evaluating at a single point loses information about which specific truth assignments are satisfying — the algorithm cannot distinguish which of the `2^V` assignments contribute to the diagonal count.

### Error 3: Single-Point Evaluation Loses Critical Information

In Sections 4 and 5, the algorithm evaluates the clause polynomials at a single numeric value (e.g., `x = 3`). This collapses the `2^V`-coefficient polynomial to a single number modulo `p`. The resulting "diagonal count" computed by the linear algebra is not the count of satisfying assignments — it is an algebraic quantity that does not reliably distinguish between satisfiable and unsatisfiable instances without exponentially many evaluations.

The Chinese Remainder Theorem approach (using multiple primes) helps reduce false-negative probability, but cannot eliminate the fundamental information loss from single-point evaluation. To reliably determine satisfiability, one would need `2^V` evaluation points — restoring the exponential cost.

### Error 4: The Certificate Generation Is Flawed

The certificate generation (Section 6) proposes fixing one variable at a time and re-running the algorithm. However:

- Each run of the basic algorithm may itself produce a false negative.
- The error probability compounds over `V` iterations: the probability of successfully recovering a certificate, given that the formula is satisfiable, is at most `(1 - ε)^V` where ε is the per-run error rate.
- More critically, the claim that "if the algorithm says the formula with `x₁ = true` is unsatisfiable, we can try `x₁ = false`" assumes the algorithm is reliable — but it is probabilistic and may give the wrong answer.

### Error 5: Incomplete Proof

The paper explicitly states it is a "semi-complete first draft." Section 4 ends with "to be completed later..." and the proofs in the appendices do not cover all cases. Key lemmas about the correctness of the off-diagonal elimination are asserted without rigorous proof.

## Why the Approach Is Appealing

The approach is interesting because:
- Linear algebra over finite fields IS an efficient technique (Gaussian elimination runs in O(n³)).
- Encoding Boolean information as polynomial coefficients is a real technique (used in, e.g., the PCP theorem and algebraic proof complexity).
- Modular arithmetic can give probabilistic correctness guarantees.

However, the fundamental barrier is that the polynomials encoding all truth assignments have size **2^V**, making the construction and manipulation of these polynomials inherently exponential.

## Broader Context

### The Representation Barrier

A fundamental barrier to polynomial-time SAT algorithms is the **representation barrier**: any data structure that faithfully encodes the complete satisfaction behavior of a k-SAT formula over `V` variables must be able to distinguish `2^V` possible truth assignments. This requires at least `2^V` bits of information. Any algorithm that works with less information (e.g., by evaluating a polynomial at one point) necessarily loses information and cannot reliably solve k-SAT.

### Algebraic Proof Complexity

Algebraic techniques (like sum-check protocols, low-degree extensions) are powerful tools in complexity theory, but they are used to prove complexity results (like IP = PSPACE), not to show that NP-hard problems can be solved efficiently. In sum-check and related protocols, the polynomial representation is used for verification (checking a prover's claims), not for finding solutions from scratch.

### The Cook-Levin Theorem

k-SAT (for k ≥ 3) is NP-complete by the Cook-Levin theorem. Any polynomial-time algorithm for k-SAT would imply P = NP. The Clay Millennium Prize of $1,000,000 remains unclaimed precisely because no such algorithm has been rigorously proven correct.

## Formalization Goals

In this directory, we formalize:

1. **The Clause Polynomial Construction**: How Groff encodes clauses as polynomials.
2. **The Multiplication-Conjunction Correspondence**: The claimed relationship between polynomial multiplication and Boolean conjunction.
3. **The Finite Field Linear System**: The 2×2 linear system used to count satisfying assignments.
4. **The Exponential Size of Polynomials**: Why the clause polynomials have 2^V coefficients.
5. **The Information Loss from Single-Point Evaluation**: Why evaluating at one point cannot determine satisfiability.
6. **The Probabilistic Nature**: Why the algorithm is at best BPP, not P.

The formalizations capture Groff's claimed proof structure while marking the key gaps with `sorry` (Lean 4) and `Admitted` (Rocq) to indicate where the argument fails to constitute a valid proof.

## References

### Primary Source

- **Original Paper**: Groff, M. (2011). "Towards P = NP via k-SAT: A k-SAT Algorithm Using Linear Algebra on Finite Fields"
  - arXiv:1106.0683v2
  - Submitted: June 3, 2011; Revised: October 1, 2011
  - Available at: https://arxiv.org/abs/1106.0683

### Context

- **Woeginger's List**: Entry #75
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Cook-Levin Theorem**: Establishes NP-completeness of SAT
- **k-SAT and NP-completeness**: Karp (1972) showed 3-SAT is NP-complete via reduction from SAT

## Key Insights

### Why P ≠ NP Is Plausible

This attempt illustrates a common pattern in failed P=NP proofs:
- The approach uses real and powerful mathematical techniques (finite fields, linear algebra, polynomial representations).
- The algorithm appears efficient when described abstractly (polynomial number of arithmetic operations).
- The exponential cost is hidden in the size of the objects being operated on (2^V-sized polynomials).

### The Size vs. Count Confusion

The core confusion in Groff's argument is between:
- **Number of arithmetic operations**: Polynomial in n and V.
- **Size of each operand**: Exponential in V (the polynomials have 2^V coefficients).

True polynomial-time algorithms must have polynomial-size inputs, polynomial-size working memory, and polynomial many operations — all at the same time. Groff's algorithm satisfies the first condition but fails the second.

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Repository README](../../../README.md) - Overview of the P vs NP problem
