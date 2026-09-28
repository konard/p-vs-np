# Solving Satisfiability by Bayesian Inference

**Author:** Michel Feldmann
**arXiv:** 1205.6658v5 (revised 2020)
**Original language:** English

---

## Abstract

We revisit the classical Boolean satisfiability problem from the perspective of Bayesian inference. We encode each Boolean variable as a conditional probability in a Kolmogorov probability space, derive a linear programming (LP) system whose feasibility is equivalent to satisfiability for "strictly satisfiable" formulas, and show that this LP system has polynomial size when the maximum clause length is bounded. Since LP feasibility is decidable in polynomial time, we conclude that 3-SAT ∈ P and therefore P = NP.

---

## 1. Introduction

The Boolean satisfiability problem (SAT) asks: given a propositional formula, is there an assignment of truth values to variables that makes the formula true? The 3-SAT variant, where every clause has at most 3 literals, is NP-complete (Cook 1971).

We approach this problem via Bayesian inference. The key idea is to represent truth values probabilistically: instead of assigning Boolean values directly, we assign probabilities. The constraints of the SAT formula become linear constraints on the probabilities.

---

## 2. Probabilistic Encoding

### 2.1 Kolmogorov Probability Space

Let (Ω, F, P) be a probability space where:
- Ω = {ω₁, ω₂, ..., ω_M} is the sample space (one state per complete truth assignment)
- F = 2^Ω is the σ-algebra (all subsets)
- P : F → [0,1] is a probability measure

### 2.2 Boolean Variables as Probabilities

For each Boolean variable X_i (i = 1, ..., N), define:
- P(i) = P(X_i = 1 | Λ) — the probability that X_i is true given background knowledge Λ
- P(i̅) = 1 - P(i) — the probability that X_i is false

### 2.3 Partial Requirements

A **partial requirement** is a conjunction of literals, e.g., X_i ∧ ¬X_j ∧ X_k. Its probability is:
- P(i, j̅, k) = P(X_i = 1, X_j = 0, X_k = 1 | Λ)

These are the "working unknowns" of the LP system.

---

## 3. Linear Programming Formulation

### 3.1 Definition 1: Complete Requirements

A **complete requirement** is a partial requirement that specifies the truth value of all N variables. It corresponds to a complete truth assignment ω ∈ Ω.

### 3.2 Definition 2: Specific Equations

For each clause C in the SAT formula, derive a **specific equation**: the sum of probabilities of all complete requirements consistent with C equals some probability value.

### 3.3 Definition 3: Working Unknowns

The **working unknowns** are the partial requirements that appear in the specific equations. These represent marginal probabilities that the LP system must determine.

### 3.4 Definition 4: Consistency Equations

**Consistency equations** ensure that the probabilities are consistent with a valid probability distribution:
- Non-negativity: P(req) ≥ 0 for all partial requirements
- Normalization: Sum of all complete requirements = 1
- Marginalization: For any partial requirement req, the sum over extensions of req equals P(req)

### 3.5 The LP System

The complete LP system consists of:
- Specific equations (one per clause)
- Consistency equations (from Definition 4)
- Non-negativity constraints (p ≥ 0)

This is a standard LP of the form: minimize 0 subject to Ap = b, p ≥ 0.

---

## 4. Main Results

### 4.1 Proposition 1: Probability Space Representation

Every complete truth assignment corresponds to exactly one complete requirement, and every complete requirement corresponds to at most one truth assignment.

### 4.2 Proposition 2: Polynomial Size

**Claim:** When the maximum clause length ℓ_max is bounded (ℓ_max ≤ 3 for 3-SAT), the total number of working unknowns is polynomial in the input size N (number of variables) and M (number of clauses).

*Proof sketch:* Each specific equation involves working unknowns with at most ℓ_max literals. Since ℓ_max ≤ 3, each unknown involves at most 3 variables. The number of distinct partial requirements of length at most 3 from N variables is O(N³). After removing duplicates, the total number of working unknowns is bounded by O(N³ · M).

### 4.3 Proposition 3: Deterministic Solutions

For a deterministic prior (where each complete requirement has probability 0 or 1), the LP system reduces to a system of linear equations with integer coefficients.

### 4.4 Proposition 4: Separability

The LP system decomposes into independent sub-systems corresponding to different "layers" of the Bayesian network. Each layer can be solved independently.

### 4.5 Proposition 5: Complete Requirements and Consistency

Every feasible solution to the LP system corresponds to a valid probability distribution over complete requirements (truth assignments).

### 4.6 Proposition 6: Truth Table Determination

**Claim:** In a "problem of strict satisfiability" (where no auxiliary variables are needed), the LP system Eq. (10) determines the truth table, i.e., the unique Boolean function of the prior.

*Proof sketch:* By definition of strict satisfiability, assigning deterministic truth values to one literal propagates to all working unknowns via the consistency equations.

### 4.7 Proposition 7 (Main Theorem): Feasibility ⟺ Satisfiability

**Claim:** When the prior is just a single Boolean function f compelled to be valid, the problem accepts a deterministic solution if and only if the Bayesian LP system Eq. (10) is feasible.

*Proof sketch:*

(⇒) If f is satisfiable, let a be a satisfying assignment. Assign probability 1 to the complete requirement corresponding to a, and 0 to all others. This gives a feasible solution to the LP.

(⇐) If the LP is feasible, there exists a valid probability distribution over complete requirements. The specific equations ensure that at least one complete requirement consistent with every clause has positive probability. This complete requirement corresponds to a satisfying assignment.

---

## 5. Algorithm

### 5.1 The Decision Procedure

**Input:** 3-SAT formula f with N variables and M clauses.

**Step 1:** Construct the LP system:
- Generate specific equations from each clause
- Determine working unknowns
- Add consistency equations

**Step 2:** Check LP feasibility using standard algorithms (ellipsoid method or interior point method).

**Step 3:** Output: SAT if LP is feasible, UNSAT otherwise.

### 5.2 Complexity Analysis

- **LP size:** O(N³ · M) variables, O(N³ · M) constraints (Proposition 2)
- **LP feasibility:** Polynomial in LP size (Khachiyan 1979)
- **Total:** Polynomial in N and M

### 5.3 Finding a Satisfying Assignment

To find an actual satisfying assignment:

**Step 1:** Check feasibility of full LP (determining satisfiability).

**Step 2:** For i = 1 to N:
  - Fix X_i = 1 and check LP feasibility of reduced system
  - If feasible, keep X_i = 1; otherwise set X_i = 0

This requires N successive LP feasibility checks, each polynomial.

---

## 6. Conclusion

We have shown that:
1. Any 3-SAT formula can be converted to an LP system of polynomial size (Proposition 2)
2. The LP system is feasible if and only if the formula is satisfiable (Proposition 7)
3. LP feasibility can be checked in polynomial time (Khachiyan 1979)

Therefore 3-SAT ∈ P, and since 3-SAT is NP-complete, P = NP.

---

## References

- Cook, S.A. (1971). The complexity of theorem proving procedures. Proc. 3rd STOC, pp. 151-158.
- Karp, R.M. (1972). Reducibility among combinatorial problems. In Complexity of Computer Computations, pp. 85-103.
- Khachiyan, L.G. (1979). A polynomial algorithm in linear programming. Soviet Mathematics Doklady, 20:191-194.
- Karmarkar, N. (1984). A new polynomial-time algorithm for linear programming. Combinatorica, 4:373-395.
- Kolmogorov, A.N. (1933). Grundbegriffe der Wahrscheinlichkeitsrechnung. Springer.
