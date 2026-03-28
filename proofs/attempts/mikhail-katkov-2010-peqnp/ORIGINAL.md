# Original Paper: Polynomial Complexity Algorithm for Max-Cut Problem

**Author:** Mikhail Katkov
**Year:** 2010 (submitted July 24, 2010; revised v2: August 5, 2010)
**arXiv ID:** [1007.4257v2](https://arxiv.org/abs/1007.4257)
**Subject Classification:** Computer Science > Computational Complexity; Combinatorics (math.CO)
**Woeginger's List:** Entry #64
**Status:** **WITHDRAWN** (withdrawn April 4, 2011)

---

## Withdrawal Notice

On April 4, 2011, the author withdrew the paper with the following statement:

> "The community convinced me that this peace of crank was written by crackpot trisector. I apologize for disturbing community."

This self-deprecating withdrawal confirms the proof contained fundamental flaws.

---

## Abstract

The paper addresses the NP-complete max-cut problem by converting it to a binary quadratic program. The author claims that for a positive semidefinite matrix Q, finding the global minimum of the polynomial function:

```
Q(α, x) = αx^T Qx + Σᵢ(xᵢ² - 1)²
```

provides a solution to the max-cut problem.

**Key claims:**
- The global minimum can be determined via polynomial-time semidefinite programming
- The sign structure is maintained at minimal points for sufficiently small α
- For α > 0 sufficiently small, the approach yields optimal solutions
- A verification method exists through quadratic form analysis

**Conclusion:** The author concludes that this methodology solves arbitrary max-cut problems in polynomial time, thereby proving P=NP.

---

## Paper Structure

### 1. Introduction

The Max-Cut problem is a well-known NP-complete problem defined as follows:

**Max-Cut Problem:** Given a weighted graph G = (V, E) with weight function w: E → ℝ, find a subset S ⊂ V that maximizes the weight of the cut δ_G(S) = {(i,j) | i ∈ S, j ∉ S}.

### 2. Reduction to Binary Quadratic Program

The paper correctly reduces Max-Cut to the following binary quadratic program (BQP):

```
minimize x^T Q x
subject to xᵢ² = 1 for all i ∈ {1,...,n}
```

where:
- x ∈ {-1, +1}ⁿ encodes the partition (xᵢ = +1 if i ∈ S, xᵢ = -1 otherwise)
- Q is derived from the weight matrix of the graph

This reduction is standard and correct.

### 3. Relaxation to Quartic Polynomial

The key idea is to relax the constrained problem to an unconstrained optimization by introducing a penalty term:

```
Q(α, x) = α x^T Q x + Σᵢ (xᵢ² - 1)²
```

where α > 0 is a small parameter.

**Claimed properties:**
1. For α > 0 sufficiently small, global minima of Q(α, x) occur at points where xᵢ² ≈ 1
2. The sign pattern of such a global minimum solves the original Max-Cut problem
3. Q(α, x) can be expressed as a sum of squares of polynomials
4. The global minimum can be found in polynomial time using semi-definite programming

### 4. Sum-of-Squares (SOS) Approach

The paper relies on results from Parrilo (2003) and Shor (1987) about sum-of-squares polynomials:

**Lemma 3.1** (from Parrilo 2003): For a polynomial f(x), finding the largest λ such that f(x) - λ is a sum of squares can be solved via semi-definite programming (SDP) in polynomial time.

**Lemma 3.3** (Katkov): For polynomials f(x) that ARE already sums of squares, the SOS lower bound equals the true minimum: f^sos = f* = min f(x).

### 5. The Core Claims

**Lemma 4.1:** For α > 0, the global minimum of Q(α, x) can be found in polynomial time via SDP.

**Theorem 4.2 (Sign Preservation):** There exists α* > 0 such that for all 0 ≤ α < α*, the sign pattern of the global minimum x*(α) matches the sign pattern of the global minimum x*(0).

**Critical Claim:** Since x*(0) satisfies xᵢ² = 1 (binary constraints), and the sign is preserved for small α > 0, solving for the global minimum of Q(α, x) gives a solution to the original Max-Cut problem.

**Conclusion:** Max-Cut can be solved in polynomial time, therefore **P=NP**.

---

## Section Details

### Section 3: Sum-of-Squares Framework

The paper introduces the concept of sum-of-squares (SOS) polynomials:

**Definition 3.2:** A polynomial f(x) is a sum of squares (SOS) if there exist polynomials p₁(x), ..., pₘ(x) such that:
```
f(x) = Σᵢ pᵢ(x)²
```

**Key Property:** If f(x) is SOS, then f(x) ≥ 0 for all x, and the minimum value is 0 if and only if all pᵢ(x) = 0 simultaneously.

**SDP Relaxation:** The paper uses the fact that checking if a polynomial is SOS can be formulated as a semidefinite program, solvable in polynomial time.

### Section 4: Main Theorems

**Theorem 4.1 (Polynomial Time via SDP):**
For any α > 0 and positive semidefinite Q, the global minimum of Q(α, x) can be computed in polynomial time using semidefinite programming.

**Theorem 4.2 (Sign Preservation - CLAIMED):**
There exists α* > 0 such that for all 0 ≤ α < α*, if x*(α) is a global minimizer of Q(α, x), then the sign pattern of x*(α) equals the sign pattern of some global minimizer x*(0) of the constrained problem (where xᵢ² = 1).

**Proof Sketch (from paper):**
1. Analyze the behavior of Q(α, x) near feasible points (where xᵢ² = 1)
2. Show that local perturbations preserve sign patterns
3. Use continuity arguments as α → 0
4. Claim that this extends to global minima

### Section 5: Certificate Extraction

**Claim:** The eigenvector corresponding to the smallest eigenvalue of the matrix representation of Q(α, x) gives the optimal binary solution.

**Algorithm:**
1. Compute α* (sufficiently small but positive)
2. Solve the SDP to find the global minimum of Q(α*, x)
3. Extract binary solution from the continuous solution via sign function: xᵢ = sign(xᵢ*(α*))
4. Return this as the optimal Max-Cut solution

---

## Equation 24 (Critical)

The paper's equation (24) attempts to establish uniqueness:

```
Δ > αn (λ²_max/2 - λ²_min/4) + o(α)
```

where:
- Δ is claimed to be "the minimum difference between cuts"
- λ_max, λ_min are eigenvalue bounds
- n is the number of vertices
- o(α) represents higher-order terms

**Critical Issue:** This equation assumes Δ > 0, but for many graphs (those with multiple optimal cuts of equal weight), Δ = 0, causing the entire argument to collapse.

---

## References (from paper)

1. **Parrilo, P. A.** (2003). "Semidefinite programming relaxations for semialgebraic problems." Mathematical Programming, Series B, 96(2), 293-320.

2. **Shor, N. Z.** (1987). "Quadratic optimization problems." Soviet Journal of Computer and Systems Sciences, 25, 1-11.

3. **Goemans, M. W., & Williamson, D. P.** (1995). "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming." Journal of the ACM, 42(6), 1115-1145.

---

## Document Details

- **Pages:** 7 (with 1 figure)
- **DOI:** https://doi.org/10.48550/arXiv.1007.4257
- **PDF Available:** Yes (see ORIGINAL.pdf in this directory)
- **Versions:**
  - v1: July 24, 2010
  - v2: August 5, 2010 (this version)
  - v3: (intermediate revision)
  - v4: April 4, 2011 (withdrawn with author's apology)

---

## Historical Context

This attempt appeared on Woeginger's famous list of P vs NP attempts as entry #64. The author's candid withdrawal statement is notable for its self-deprecating humor while acknowledging the fundamental flaws identified by the community.

The attempt is pedagogically valuable because:
1. It demonstrates common pitfalls in continuous relaxation approaches
2. It shows the gap between local properties and global guarantees
3. It illustrates why SDP approximations have integrality gaps
4. It highlights the importance of uniqueness assumptions in optimization arguments

---

**Note:** This markdown conversion preserves the structure and key content of the original paper. For exact mathematical details, figures, and complete proofs (flawed as they are), refer to ORIGINAL.pdf in this directory.
