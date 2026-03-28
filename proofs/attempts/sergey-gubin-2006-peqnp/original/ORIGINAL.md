# Original Paper: A Polynomial Time Algorithm for The Traveling Salesman Problem

**Author:** Sergey Gubin
**Year:** 2006
**arXiv ID:** cs/0610042
**Original Source:** https://arxiv.org/abs/cs/0610042

---

## Abstract

> The ATSP polytope can be expressed by asymmetric polynomial size linear program.

---

## Paper Summary

Sergey Gubin's 2006 paper attempts to prove P = NP by presenting what he claims is a polynomial-time algorithm for the Traveling Salesman Problem (TSP). The approach uses linear programming techniques.

### Main Claims

1. **Claim 1 (LP Formulation):** The Asymmetric Traveling Salesman Problem polytope can be captured by a polynomial-sized linear program.

2. **Claim 2 (Integrality):** All extreme points of this LP are integral and correspond to valid TSP tours.

3. **Claim 3 (Polynomial Time):** Since LP can be solved in polynomial time, TSP can be solved in polynomial time.

4. **Claim 4 (P = NP):** Since TSP is NP-complete, this proves P = NP.

### Approach 1: ATSP via Linear Programming

The paper proposes an LP formulation with:
- O(n²) variables representing edge selections
- O(n²) constraints for flow conservation and subtour elimination
- The claim that this captures exactly the set of Hamiltonian cycles

### Approach 2: SAT to 2-SAT Reduction

A secondary claim in the paper involves reducing satisfiability (SAT) to 2-SAT:
- Transform any CNF formula to 2-CNF
- Claim polynomial blowup in formula size
- Use polynomial-time 2-SAT algorithm to solve original problem

---

## Technical Formulation (Reconstructed)

### ATSP LP Formulation

For a directed graph G = (V, E) with n vertices:

**Variables:**
- x_{ij} ∈ {0, 1} for each edge (i, j) ∈ E

**Objective:**
- Minimize Σ_{(i,j) ∈ E} c_{ij} · x_{ij}

**Constraints:**
1. **Flow out:** Σ_j x_{ij} = 1 for all i
2. **Flow in:** Σ_i x_{ij} = 1 for all j
3. **Subtour elimination:** Various formulations attempted

The critical error is in the subtour elimination constraints, which Gubin claimed could be expressed with polynomial many linear constraints while maintaining integrality of extreme points.

### SAT to 2-SAT Reduction

For a CNF formula φ with clauses of size k > 2:

**Proposed transformation:**
- Introduce auxiliary variables to break down larger clauses
- Convert each k-literal clause to multiple 2-literal clauses
- Claim: |φ'| = O(|φ|^c) for some constant c

The critical error is that this transformation actually requires exponentially many clauses to correctly capture the satisfiability of the original formula.

---

## Why These Approaches Fail

### Error 1: Non-Integral Extreme Points (Hofman 2006)

Hofman's counter-example demonstrates:
- There exist extreme points of Gubin's LP that are fractional
- These fractional points do not correspond to any valid tour
- Therefore, solving the LP does not directly give TSP solutions

**Key Insight:** A polynomial-sized LP can have non-integral vertices, even if the integer solutions form a valid combinatorial structure. The integrality of the LP relaxation cannot be assumed without proof.

### Error 2: Exponential Blowup in SAT Reduction (Christopher et al. 2008)

The SAT to 2-SAT reduction fails because:
- Converting a k-clause to 2-clauses requires exponential many clauses
- Example: (x₁ ∨ x₂ ∨ x₃) cannot be expressed as polynomially many 2-clauses
- The standard Tseitin transformation introduces auxiliary variables but each k-clause still needs O(k) new clauses

**Key Insight:** The expressive power of 2-SAT is fundamentally weaker than 3-SAT. No polynomial reduction can bridge this gap while preserving satisfiability equivalence.

---

## Historical Context

- **Submission:** October 2006
- **Revisions:** Multiple through September 2008
- **Conference:** 22nd Mountain West Conference on Combinatorics (2008)
- **Status:** Refuted by Hofman (2006) and Christopher, Huo, Jacobs (2008)
- **Woeginger's List:** Entry #33

---

## Note on Original PDF

The full original paper is available at:
- https://arxiv.org/pdf/cs/0610042.pdf

This markdown document provides a summary and reconstruction of the main arguments. For the exact formulations and proofs as written by Gubin, please refer to the original PDF.
