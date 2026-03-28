# Formalization: Antano Maknickas (2011) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 85 (from Woeginger's list)
- **Author**: Algirdas Antano Maknickas
- **Year**: 2011 (published March 2011, revised March 2012)
- **Claim**: P = NP
- **Paper**: "How to solve kSAT in polynomial time"
- **Source**: arXiv:1203.6020v2 [cs.CC] (6 pages)
- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #85)

## Summary

In March 2011, Algirdas Antano Maknickas published a paper claiming to prove that **P = NP** by showing that k-SAT can be solved in O(n^3.5) time. The paper uses "multi-nary logic analytic formulas in modulo form" to transform SAT instances into systems of linear inequalities, then claims to solve these using linear programming.

The paper concludes: "every mathematical problem is solvable in polynomial time if exist full, appropriate and correct knowledge basis for it and the time to get each item of knowledge basis is match less than calculation time on this items."

## The Main Argument

### Overview

Maknickas proposes a three-step approach to solve k-SAT:

1. **Transform Boolean variables to real numbers**: Convert each Boolean variable Xi ∈ {0,1} to a real variable Xi ∈ ℝ
2. **Formulate as linear programming**: Express the k-SAT problem as a linear programming (LP) problem with constraints
3. **Recover Boolean solution**: Use a floor function g₀²(Xi) = ⌊Xi⌋ (mod 2) to convert the LP solution back to Boolean values

### Detailed Steps

#### Step 1: Multi-nary Logic Functions (Section 1)

The paper introduces a function:
```
gₙᵏ(a) = ⌊a⌋ + k (mod n)
```

For n=2 (binary logic), this allegedly generates all Boolean functions.

**LEMMA 1**: If n=2, function gₙᵏ(a) generates one-variable binary logic functions
**LEMMA 2**: If n=2, function gₙᵏ(a*b) generates two-variable binary logic functions
**LEMMA 3**: If n>2, generalizes to multi-nary logic
**LEMMA 4**: If n>2, generalizes to two-variable multi-nary logic

#### Step 2: Transform k-SAT to Linear Programming

**For 2-SAT** (Theorems 1-2):
- Express (X₁ ∨ X₂) ∧ (X₃ ∨ X₄) ∧ ... as a nested function μ
- Convert to: max β₂(X₁, X₂, ..., Xₙ)
- Reduce to system: Xi-1 + Xi ≤ 2 where Xi ≥ 0
- Claim: Solve with linear programming in O(n^3.5)

**For 3-SAT** (Theorems 3-4):
- Express (X₁ ∨ X₂ ∨ X₃) ∧ ... as nested μ functions
- Convert to: max β₃(X₁, X₂, ..., Xₙ)
- Reduce to system: Xi-2 + Xi-1 + Xi ≤ 3 where Xi ≥ 0
- Claim: Solve with linear programming in O(n^3.5)

**For k-SAT** (Theorems 5-6):
- Generalize to k variables per clause
- System of constraints: ∑ᵢ₌ⱼʲ⁺ᵏ⁻¹ Xi ≤ k where Xi ≥ 0
- Claim: Solve with linear programming in O(n^3.5)

#### Step 3: Recover Boolean Solution

After solving the LP, convert back to Boolean:
```
X̃i = g₀²(Xi) = ⌊Xi⌋ (mod 2), ∀i ∈ {1, 2, ..., n}
```

## The Fatal Error

### The Critical Flaw: Invalid Conversion

**The fundamental error occurs in the conversion from Boolean satisfiability to linear programming optimization.**

#### Problem 1: Wrong Problem Being Solved

The paper transforms:
- **Original problem**: Find Xi ∈ {0,1} such that the CNF formula evaluates to TRUE
- **Transformed problem**: Find Xi ∈ ℝ (Xi ≥ 0) that maximizes some objective function

**These are completely different problems!**

#### Problem 2: The Relaxation Doesn't Preserve Satisfiability

For 3-SAT with clause (X₁ ∨ X₂ ∨ X₃):
- **Boolean**: At least ONE variable must be TRUE (value 0 in the paper's convention)
- **LP constraint**: X₁ + X₂ + X₃ ≤ 3 with Xi ≥ 0

The LP constraint X₁ + X₂ + X₃ ≤ 3 is satisfied by:
- X₁ = X₂ = X₃ = 1 (all FALSE in Boolean) ✓ Satisfies LP
- X₁ = X₂ = X₃ = 0.5 ✓ Satisfies LP
- X₁ = 0, X₂ = 0, X₃ = 0 ✓ Satisfies LP

But only some of these correspond to valid Boolean assignments that satisfy the original clause!

#### Problem 3: The Floor Function Doesn't Recover Valid Solutions

After solving the LP, the paper uses X̃i = ⌊Xi⌋ (mod 2) to convert back to Boolean.

**Counterexample**:
Consider an unsatisfiable 3-SAT instance:
```
(X₁ ∨ X₂ ∨ X₃) ∧ (¬X₁ ∨ ¬X₂ ∨ X₃) ∧ (X₁ ∨ ¬X₂ ∨ ¬X₃) ∧ (¬X₁ ∨ X₂ ∨ ¬X₃)
```

The LP relaxation may find a feasible solution in real numbers (e.g., all Xi = 0.5), which when rounded, may or may not satisfy the original formula. **There is no guarantee the rounded solution satisfies the original CNF.**

#### Problem 4: Maximization vs. Satisfiability

The paper transforms SAT (a decision problem: "does a satisfying assignment exist?") into an optimization problem ("maximize some function"). These are fundamentally different:

- **SAT**: Needs to find ANY assignment that makes formula TRUE
- **LP maximization**: Finds assignment that maximizes an objective (which may not correspond to satisfiability)

The max operator in equations (12), (20), (27) assumes that maximizing the function will yield a satisfying assignment, but this is never proven and is in fact **false**.

#### Problem 5: Ignores the Disjunctive Structure

In Boolean logic:
- (X₁ ∨ X₂ ∨ X₃) = TRUE means **at least one** of {X₁, X₂, X₃} is TRUE

The paper's encoding with arithmetic sums completely loses this disjunctive constraint. The LP constraint X₁ + X₂ + X₃ ≤ 3 doesn't encode "at least one variable is true"—it just says the sum is bounded.

### Why This Doesn't Work: Concrete Example

**Example 3-SAT instance**:
```
F = (X₁ ∨ X₂ ∨ X₃)
```

**Boolean satisfying assignments** (using 0=TRUE, 1=FALSE):
- X₁=0, X₂=1, X₃=1 ✓
- X₁=1, X₂=0, X₃=1 ✓
- X₁=1, X₂=1, X₃=0 ✓
- X₁=0, X₂=0, X₃=1 ✓
- etc. (any assignment with at least one 0)

**Non-satisfying assignment**:
- X₁=1, X₂=1, X₃=1 ✗ (all FALSE)

**LP formulation** (per the paper):
- Constraint: X₁ + X₂ + X₃ ≤ 3, Xi ≥ 0
- Maximize: some function

**LP solution**: X₁=1, X₂=1, X₃=1 satisfies the LP constraint!
- Sum: 1 + 1 + 1 = 3 ≤ 3 ✓

But this corresponds to the **unsatisfying** Boolean assignment (all FALSE).

**The paper never proves that the LP solution, when converted via the floor function, will satisfy the original CNF formula.**

## Known Refutation

This proof has **not been accepted** by the mathematical or computer science community. The errors are:

1. **Invalid problem transformation**: LP relaxation doesn't preserve satisfiability
2. **No correctness proof**: Never proves the floor function recovers a valid solution
3. **Ignores NP-completeness barriers**: If this worked, all of NP-complete theory would collapse
4. **Peer review**: Not published in peer-reviewed venue, only on arXiv

The approach is a variation of **LP relaxation**, which is well-studied in approximation algorithms but is known to **not solve** NP-complete problems exactly in polynomial time.

## Formalization Goal

Our formalizations in Rocq, Lean, and Isabelle will:

1. **Define the transformation** from k-SAT to the LP formulation
2. **Formalize the recovery function** (floor + modulo)
3. **Prove the gap**: Show that the LP solution doesn't necessarily yield a valid SAT solution
4. **Construct counterexamples**: Explicit SAT instances where the method fails

This will make the error **formally verifiable** and serve as an educational resource.

## Files

- **[rocq/MaknickasAttempt.v](rocq/MaknickasAttempt.v)** - Rocq formalization showing the gap
- **[lean/MaknickasAttempt.lean](lean/MaknickasAttempt.lean)** - Lean 4 formalization
- **[isabelle/MaknickasAttempt.thy](isabelle/MaknickasAttempt.thy)** - Isabelle/HOL formalization

## References

### Original Paper
- Maknickas, A. A. (2012). "How to solve kSAT in polynomial time." arXiv:1203.6020v2 [cs.CC]
  - Link: https://arxiv.org/abs/1203.6020

### Related Incorrect Proofs Cited in Paper
- Maknickas, A. A. (2010). "Finding of k in Fagin's R. Theorem 24." arXiv:1012.5804v1
- Weiss, A. (2011). "A Polynomial Algorithm for 3-sat." (unpublished)
- Kardash, S. (2011). "Algorithmic complexity of pair cleaning method." arXiv:1108.0408v1
- Groff, M. (2011). "Towards P = NP via k-SAT." arXiv:1106.0683v2

### Why LP Relaxation Doesn't Solve NP-Complete Problems
- Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.
  - Chapter 15: "Linear Programming and Semidefinite Programming"
  - Explains why LP relaxations are used for approximation, not exact solutions

### Linear Programming Complexity
- Karmarkar, N. (1984). "A new polynomial-time algorithm for linear programming." *Combinatorica*, 4(4), 373-395.
  - The paper correctly cites that LP can be solved in polynomial time
  - But this doesn't help because the LP doesn't solve the original SAT problem!

## Educational Value

This formalization demonstrates:

1. **Type mismatch**: Boolean satisfiability vs. real-valued optimization
2. **Relaxation gaps**: Why relaxing constraints changes the problem
3. **Importance of correctness proofs**: Claims require rigorous proof
4. **Proof verification**: How formal methods catch subtle errors

## Status

- ✅ Rocq formalization: Complete - identifies the gap
- ✅ Lean formalization: Complete - identifies the gap
- ✅ Isabelle formalization: Complete - identifies the gap
- ✅ Error documentation: Complete

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Parent Issue #44](https://github.com/konard/p-vs-np/issues/44) | [This Issue #79](https://github.com/konard/p-vs-np/issues/79)
