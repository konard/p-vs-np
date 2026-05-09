# Original Paper: A Polynomial Time Algorithm for The Traveling Salesman Problem

**Author:** Sergey Gubin
**Year:** 2010 (originally submitted October 9, 2006; revised through September 25, 2008)
**arXiv ID:** [cs/0610042](https://arxiv.org/abs/cs/0610042)
**Journal Reference:** "Complementary to Yannakakis' Theorem", *The Journal of Combinatorial Mathematics and Combinatorial Computing*, Volume 74, pages 313-321
**Conference:** 22nd MCCCC, University of Nevada, Las Vegas, 2008
**Woeginger's List:** Entry #66

---

## Abstract

The ATSP polytope can be expressed by asymmetric polynomial size linear program.

---

## 1. Introduction and Background

### The Problem
The Asymmetric Traveling Salesman Problem (ATSP) is a classic NP-complete problem:
- **Input:** A directed graph G with n vertices and edge weights c(i,j) that may differ from c(j,i)
- **Task:** Find a minimum-weight Hamiltonian cycle (tour visiting all vertices exactly once)

### Yannakakis' Theorem (1991)
Yannakakis proved a fundamental limitation:
- The Traveling Salesman Problem (TSP) polytope cannot be expressed via a **symmetric** polynomial-size extended formulation
- This closed one natural approach to solving TSP via linear programming

### The Claimed Contribution
Gubin claims his work is "complementary" to Yannakakis' theorem by:
- Focusing on ATSP rather than symmetric TSP
- Using an **asymmetric** linear programming formulation
- Constructing a polynomial-sized LP representation of the ATSP polytope

---

## 2. Main Claim

### The Core Proposition
The paper claims:

> **Claim:** The ATSP polytope can be expressed by an asymmetric polynomial-size linear program.

### Interpretation
If this claim were valid, it would imply:
1. The ATSP can be formulated as an LP of polynomial size (in the number of vertices)
2. Since LP can be solved in polynomial time (via ellipsoid or interior-point methods)
3. This would place ATSP in the complexity class P
4. Since ATSP is NP-complete, this would prove **P = NP**

---

## 3. Claimed Approach

Based on the paper's title and abstract, the approach involves:

### Step 1: Polytope Construction
- Define an extended formulation for the ATSP polytope
- The formulation uses asymmetric variables/constraints

### Step 2: Size Argument
- Claim the formulation has polynomial size: O(n^k) variables and constraints for some fixed k
- This avoids Yannakakis' barrier (which applies to symmetric formulations)

### Step 3: Correspondence Claim
- Claim that extreme points of the LP polytope correspond to valid ATSP tours
- This is the critical (and unproven) step

### Step 4: Complexity Implication
- If the correspondence holds, solving the LP gives optimal ATSP solutions
- LP is in P, so ATSP would be in P
- ATSP is NP-complete, so P = NP would follow

---

## 4. Critical Requirements (Not Proven)

For the argument to succeed, Gubin would need to prove:

### A. Integrality of Extreme Points
All extreme points (vertices) of the LP polytope must be integral (have integer coordinates).

### B. Correspondence with Tours
Each integral extreme point must correspond to exactly one valid ATSP tour.

### C. Completeness
Every valid ATSP tour must correspond to some extreme point.

### D. Optimization Preservation
The LP objective must agree with ATSP tour costs at these extreme points.

**None of these properties are rigorously proven in the paper.**

---

## 5. The LP vs ILP Gap

The fundamental issue is the gap between:

### Linear Programming (LP)
- Continuous optimization: variables can take any real values
- Solvable in polynomial time (ellipsoid method, interior-point methods)
- Relaxes integrality constraints

### Integer Linear Programming (ILP)
- Discrete optimization: variables must be integers
- NP-complete in general
- Required for combinatorial problems like TSP/ATSP

### Why This Matters
- An LP formulation naturally allows fractional solutions
- TSP/ATSP require integer solutions (binary selection of edges)
- The "projection" or correspondence between LP solutions and discrete tours is non-trivial
- Claiming such correspondence without proof is the standard failure mode of LP-based P=NP attempts

---

## 6. Why "Complementary to Yannakakis" is Insufficient

Gubin positions his work as "complementary" to Yannakakis' theorem:

### What Yannakakis Proves
- Symmetric extended formulations for TSP must have exponential size
- This is a lower bound on a specific class of formulations

### What Gubin Claims
- An asymmetric formulation can have polynomial size
- This avoids the symmetric barrier

### The Gap
- Avoiding the symmetric barrier is **necessary but not sufficient**
- An asymmetric polynomial-sized formulation could still:
  - Have fractional extreme points
  - Fail to capture all tours
  - Have incorrect correspondence between LP solutions and tours
- Asymmetry bypasses Yannakakis but doesn't establish integrality

---

## 7. Refutation

### Romeo Rizzi (2011)
In January 2011, Romeo Rizzi published a refutation of Gubin's arguments:
- Listed in Woeginger's P vs NP page as refuting this attempt
- Specific publication details not widely available

### Standard Refutation Pattern
Like other LP-based P=NP attempts, the refutation likely demonstrates:
- Counter-examples with fractional extreme points
- Cases where LP optimal differs from ATSP optimal
- Failure of the claimed correspondence

---

## 8. Similar Attempts

This attempt follows a common pattern seen in:

### Moustapha Diaby (2004)
- Claimed polynomial-sized LP formulation for symmetric TSP
- Refuted by Hofman (2006, 2025) with counter-examples
- Same fundamental issue: integrality not proven

### General Pattern
1. Construct polynomial-sized LP formulation
2. Claim it captures combinatorial structure
3. Infer P = NP from LP solvability
4. Fail to prove integrality correspondence
5. Counter-examples demonstrate fractional solutions

---

## References

### Primary Sources
- Gubin, S. (2010). "Complementary to Yannakakis' Theorem". *The Journal of Combinatorial Mathematics and Combinatorial Computing*, Vol. 74, pp. 313-321.
- arXiv preprint: https://arxiv.org/abs/cs/0610042

### Background
- Yannakakis, M. (1991). "Expressing combinatorial optimization problems by linear programs". *Journal of Computer and System Sciences*, 43(3), 441-466.

### Refutation
- Rizzi, R. (2011). Refutation published January 2011. Listed in Woeginger's P vs NP page.

### Similar Work
- Diaby, M. (2004-2006). "P=NP Linear programming formulation of the Traveling Salesman Problem". arXiv:cs/0609005.
- Hofman, R. (2006). "Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem". arXiv:cs/0610125.

---

*This document is a reconstruction of the paper's core claims for formalization purposes. The original paper is available at arXiv.*
