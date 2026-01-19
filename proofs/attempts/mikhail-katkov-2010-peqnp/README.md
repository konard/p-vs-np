# Mikhail Katkov (2010) - P=NP Attempt

**Attempt ID**: 64
**Author**: Mikhail Katkov
**Year**: 2010
**Claim**: P=NP
**Paper**: [arXiv:1007.4257v2](http://arxiv.org/abs/1007.4257) - "Polynomial complexity algorithm for Max-Cut problem"
**Status**: **INVALID & WITHDRAWN** - Author withdrew the paper on April 4, 2011

---

## Summary

In July 2010, Mikhail Katkov claimed to prove P=NP by constructing a polynomial-time algorithm for the NP-complete Max-Cut problem. The approach attempted to solve the binary quadratic program formulation of Max-Cut using semi-definite programming on a sum-of-squares polynomial relaxation. The author withdrew the paper in April 2011, acknowledging fundamental flaws in the work.

## Main Argument

### 1. Problem Formulation: Max-Cut

The **Max-Cut problem** is defined as follows: Given a weighted graph G = (V, E) with weight function w: E → ℝ, find a subset S ⊂ V that maximizes the weight of the cut δ_G(S) = {(i,j) | i ∈ S, j ∉ S}.

This is a well-known NP-complete problem.

### 2. Reduction to Binary Quadratic Program

The paper correctly reduces Max-Cut to the following binary quadratic program (BQP):

```
minimize x^T Q x
subject to x_i^2 = 1 for all i
```

where x ∈ {-1, +1}^n encodes the partition (x_i = +1 if i ∈ S, x_i = -1 otherwise), and Q is derived from the weight matrix.

This reduction is standard and correct.

### 3. Relaxation to Quartic Polynomial

The key idea is to relax the constrained problem to an unconstrained optimization by introducing a penalty term:

```
Q(α, x) = α x^T Q x + Σ_i (x_i^2 - 1)^2
```

**Claimed properties:**
1. For α > 0 sufficiently small, global minima of Q(α, x) occur at points where x_i^2 ≈ 1
2. The sign pattern of such a global minimum solves the original Max-Cut problem
3. Q(α, x) can be expressed as a sum of squares of polynomials
4. The global minimum can be found in polynomial time using semi-definite programming

### 4. Sum-of-Squares (SOS) Approach

The paper relies on results from [Par03, Sho87] about sum-of-squares polynomials:

**Lemma 3.1** (from [Par03]): For a polynomial f(x), finding the largest λ such that f(x) - λ is a sum of squares can be solved via semi-definite programming (SDP) in polynomial time.

**Lemma 3.3** (Katkov): For polynomials f(x) that ARE already sums of squares, the SOS lower bound equals the true minimum: f^sos = f* = min f(x).

### 5. The Core Claims

**Lemma 4.1**: For α > 0, the global minimum of Q(α, x) can be found in polynomial time via SDP.

**Theorem 4.2**: There exists α* > 0 such that for all 0 ≤ α < α*, the sign pattern of the global minimum x*(α) matches the sign pattern of the global minimum x*(0).

**Critical Claim**: Since x*(0) satisfies x_i^2 = 1 (binary constraints), and the sign is preserved for small α > 0, solving for the global minimum of Q(α, x) gives a solution to the original Max-Cut problem.

**Conclusion**: Max-Cut can be solved in polynomial time, therefore P=NP.

## The Errors

The author himself acknowledged the work as fundamentally flawed. The withdrawal notice (April 4, 2011) states:

> "The community convinced me that this peace [sic] of crank was written by crackpot trisector. I apologize for disturbing community."

While the author's self-deprecating withdrawal doesn't specify the exact errors, several critical flaws can be identified:

### Error 1: The Uniqueness Gap (Section 4.1 & Equation 24)

**Location**: Pages 5-6, especially equation (24)

**The Problem**: The paper attempts to show that for sufficiently small α, the global minimum is **unique** and preserves the sign pattern from α = 0. Equation (24) claims:

```
Δ > αn (λ²_max/2 - λ²_min/4) + o(α)
```

where Δ is "the minimum difference between cuts."

**Why This Fails**:
1. **Δ is not well-defined**: For a general graph, there's no guarantee of a positive minimum gap between distinct cut values
2. **Uniqueness is not guaranteed**: Even if the Max-Cut problem has a unique optimal solution, the relaxed problem Q(α, x) can have:
   - Multiple global minima
   - Continuous manifolds of optimal solutions as α → 0
   - Bifurcations where solutions split as α changes
3. **The asymptotic analysis is incomplete**: The o(α) terms are not controlled, and higher-order effects can dominate

### Error 2: Sign Preservation (Theorem 4.2)

**Location**: Pages 3-4

**The Problem**: Theorem 4.2 claims that for small enough α, the sign pattern is preserved: signum(x_k(α)) = signum(x_k(0)).

**Why This Fails**:
1. **Proof only handles local minima**: The "proof" analyzes perturbations near feasible points x_0 with x_i^2 = 1, but doesn't establish that these remain **global** minima
2. **Bifurcation ignored**: As α → 0, the global minimum can jump discontinuously between different solution branches
3. **Multiple cuts with equal weight**: If there are multiple optimal Max-Cuts (common in practice), the global minimum can wander between them as α changes

**Concrete counterexample intuition**: Consider a graph where two different cuts have equal weight. At α = 0, both corresponding binary solutions are global minima. For α > 0, the continuous relaxation might have a global minimum at some "averaged" point that doesn't correspond to either original solution, or the minimum might jump between regions unpredictably.

### Error 3: The SDP Relaxation Gap

**Location**: Throughout, especially Section 3

**The Problem**: The paper correctly states that Q(α, x) is a sum of squares and can be minimized via SDP. However:

1. **SDP finds f^sos, not necessarily f***: While Lemma 3.3 correctly states f^sos = f* for SOS polynomials, this equality holds over **all of ℝ^n**
2. **Local vs global minima**: The SDP finds the global minimum over all real vectors x ∈ ℝ^n, but this might not correspond to a feasible solution of the original BQP
3. **Certificate extraction (Section 5)**: The claim that the sign of the eigenvector corresponding to the monomials x_i gives the solution is heuristic and not rigorously proven

### Error 4: Complexity Analysis Gap

**Location**: Section 6, equation (24), Section 4.1

**The Problem**: The paper doesn't address:

1. **How to choose α**: The value of α* depends on unknown properties of the optimal solution (like the gap Δ)
2. **Iteration complexity**: If α must be exponentially small (e.g., α < 2^(-n)), the precision requirements for the SDP solver could become exponential
3. **Bit complexity**: No analysis of the precision needed to distinguish different solutions

### Error 5: Ignoring Known Barriers

The paper doesn't acknowledge or address the known barriers to proving P=NP:

1. **Relativization** (Baker-Gill-Solovay, 1975): The approach doesn't clearly overcome this barrier
2. **Natural Proofs** (Razborov-Rudich, 1997): The method doesn't address this limitation
3. **SDP limitations**: SDP relaxations for Max-Cut are known to have integrality gaps (Goemans-Williamson, 1995)

## What the Paper Got Right

1. ✓ Correct formulation of Max-Cut as BQP (Section 2)
2. ✓ Valid construction of the penalty function Q(α, x) (Section 4)
3. ✓ Correct application of SOS theory (Section 3, citing [Par03])
4. ✓ Q(α, x) is indeed a sum of squares and can be handled by SDP
5. ✓ The perturbation analysis in Section 4.1 is mathematically reasonable (though incomplete)

## What the Paper Got Wrong

1. ✗ **Theorem 4.2 is not proven**: Sign preservation for global minima is not established
2. ✗ **Uniqueness is not proven**: The claim that there's a unique global minimum for small α is unjustified
3. ✗ **No handling of degeneracies**: Graphs with multiple optimal cuts are not addressed
4. ✗ **Gap in equation (24)**: The minimum difference Δ is not well-defined and can be zero
5. ✗ **Certificate extraction (Section 5) is heuristic**: The connection between SDP solution structure and the Max-Cut solution is not rigorous
6. ✗ **No complexity analysis for α**: The required value of α is not constructively computed
7. ✗ **Withdrawal by author**: The author himself acknowledged fundamental flaws

## Known Refutations

### Author's Withdrawal

The strongest "refutation" is the author's own withdrawal on April 4, 2011:

> "The community convinced me that this peace of crank was written by crackpot trisector. I apologize for disturbing community."

This self-deprecating statement (comparing himself to someone attempting geometric trisection, a proven impossibility) indicates that the author was convinced by the community that the approach was fundamentally flawed.

### Theoretical Impossibility

If the approach worked, it would:
1. Solve Max-Cut in polynomial time
2. Prove P=NP
3. Contradict the overwhelming consensus and decades of failed attempts

### SDP Integrality Gaps

The Goemans-Williamson algorithm (1995) for Max-Cut uses a different SDP relaxation and achieves a 0.878-approximation. The existence of this approximation ratio proves that SDP relaxations for Max-Cut have **integrality gaps** - the SDP solution is not generally integral.

## Formalization Strategy

Our formalization demonstrates the incompleteness of the proof by:

1. **Defining the Max-Cut problem**: Formalizing graphs, cuts, and the BQP formulation
2. **Formalizing the relaxation**: Defining Q(α, x) and the SOS approach
3. **Stating Theorem 4.2 as an axiom**: Representing the unproven claim
4. **Identifying the gap**: Showing that Theorem 4.2 is not proven in the paper
5. **Noting the withdrawal**: Recording that the author acknowledged the flaw

## Implementation Structure

- **`coq/KatkovAttempt.v`**: Coq formalization
- **`lean/KatkovAttempt.lean`**: Lean 4 formalization
- **`isabelle/KatkovAttempt.thy`**: Isabelle/HOL formalization
- **`paper/katkov-2010-v2.pdf`**: The original paper (version 2, before withdrawal)

Each formalization:
1. Defines the Max-Cut problem and BQP formulation
2. Formalizes the relaxation Q(α, x)
3. States the key claims (Theorem 4.2, uniqueness)
4. Identifies the proof gaps
5. Notes the author's withdrawal

## Key Lessons

### Optimistic Relaxation

The idea of relaxing hard constraints with penalty terms is sound in principle, but:
- **Global vs local**: Proving that a local property (feasibility) holds at the global minimum is much harder
- **Uniqueness matters**: Degeneracies and multiple solutions complicate the analysis
- **Continuous relaxations**: Moving from discrete to continuous problems introduces new challenges

### SDP is Not Magic

While SDP is powerful, it doesn't automatically solve NP-hard problems:
- **Integrality gaps exist**: SDP relaxations often have non-integral optimal solutions
- **Rounding is hard**: Extracting a discrete solution from a continuous one is non-trivial
- **Approximation ≠ Exact**: SDP gives good approximations (e.g., Goemans-Williamson), not exact solutions

### The Importance of Rigorous Proofs

The paper makes several claims without complete proofs:
- Theorem 4.2 (sign preservation)
- Uniqueness of the global minimum
- Certificate extraction (Section 5)

In complexity theory, where the stakes are high (P vs NP), every step must be rigorously proven.

## Barriers Not Addressed

The paper does not address known barriers to proving P=NP:
- **Relativization** (Baker-Gill-Solovay, 1975)
- **Natural Proofs** (Razborov-Rudich, 1997)
- **Algebrization** (Aaronson-Wigderson, 2008)

## References

### The Original Paper

- Katkov, M. (2010). "Polynomial complexity algorithm for Max-Cut problem." arXiv:1007.4257v2 [cs.CC]
  - URL: https://arxiv.org/abs/1007.4257
  - **Status**: Withdrawn by author on April 4, 2011

### Background on Max-Cut

- Karp, R. M. (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, 85-104.
  - Proved Max-Cut is NP-complete
- Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.* W. H. Freeman.

### SDP and Approximation Algorithms

- Goemans, M. X., & Williamson, D. P. (1995). "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming." *Journal of the ACM*, 42(6), 1115-1145.
  - The famous 0.878-approximation for Max-Cut using SDP
  - Proves integrality gaps exist for Max-Cut SDP relaxations

### Sum-of-Squares

- Parrilo, P. A. (2003). "Semidefinite programming relaxations for semialgebraic problems." *Mathematical Programming*, 96(2), 293-320.
  - [Par03] in the paper - foundation for the SOS approach
- Shor, N. Z. (1987). "Class of global minimum bounds of polynomial functions." *Cybernetics and Systems Analysis*, 23(6), 731-734.
  - [Sho87] in the paper - early work on SOS relaxations

### P vs NP

- Cook, S. A. (1971). "The complexity of theorem proving procedures." *Proceedings of the 3rd ACM Symposium on Theory of Computing*, 151-158.
- Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP question." *SIAM Journal on Computing*, 4(4), 431-442.

## Woeginger's List

This attempt appears as **Entry #64** in Gerhard Woeginger's famous list of P vs NP attempts:
- URL: https://www.win.tue.nl/~gwoegi/P-versus-NP.htm
- Category: [Equal] (claims P=NP)
- Year: 2010 (July)

## Verification Status

- ✅ Coq formalization: Compiles and identifies the proof gaps
- ✅ Lean formalization: Type-checks and documents the errors
- ✅ Isabelle formalization: Verified and notes the withdrawal

## Conclusion

Mikhail Katkov's 2010 attempt to prove P=NP via a sum-of-squares relaxation of the Max-Cut problem contains multiple fundamental flaws:

1. **Theorem 4.2 (sign preservation) is not proven**
2. **Uniqueness of the global minimum is not established**
3. **The gap Δ in equation (24) can be zero**
4. **Certificate extraction is heuristic, not rigorous**
5. **The author himself withdrew the paper**, acknowledging it was fundamentally flawed

The attempt demonstrates the difficulty of using continuous relaxations to solve discrete optimization problems, and highlights the importance of rigorous proofs in complexity theory.

## License

This formalization is provided for educational and research purposes under the repository's main license (The Unlicense).

---

**Navigation**: [↑ Back to Proofs](../../) | [Repository Root](../../../README.md) | [Issue #466](https://github.com/konard/p-vs-np/issues/466)
