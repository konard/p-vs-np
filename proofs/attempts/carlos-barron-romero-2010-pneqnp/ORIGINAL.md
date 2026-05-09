# The Complexity Of The NP-Class
**Author**: Carlos Barron-Romero
**Year**: 2010
**Source**: arXiv:1006.2218v1 [cs.CC]
**Submitted**: June 11, 2010

---

## Abstract (paraphrased)

This paper studies the complexity of problems in the NP class, focusing on the
General Assignment Problem (GAP) and the Traveling Salesman Problem (TSP). The
paper analyzes the structure of the search space for these problems and argues
that NP problems cannot have polynomial-time algorithms for "checking their solution."
The paper also studies the Lennard-Jones cluster optimization problem as an example
of NP complexity. The conclusion is that P ≠ NP.

---

## Core Claim

**Proposition 1.1**: "The problems of the NP-Class have not a polynomial algorithm
for checking their solution."

---

## Main Argument

### Section 1: Problem Definition

The paper defines NP problems as combinatorial optimization problems with large
search spaces. For TSP with n cities:
- Number of possible Hamiltonian cycles: (n-1)!
- For n = 20: (20-1)! = 19! ≈ 1.2 × 10^17 possible tours

### Section 6: GAP and TSP Analysis

The paper analyzes the research space of GAP and TSP:

**Proposition 6.9**: "The 2D Euclidian TSPₙ of the NP-Class have a polynomial
algorithm for checking their solution."

The paper argues that for 2D Euclidean instances, geometric properties allow
for efficient (claimed polynomial) algorithms.

**Proposition 6.12**: "An arbitrary and large GAPₙ of the NP-Class has not a
polynomial algorithm for checking their solution."

For arbitrary GAP/TSP instances, the paper argues that one must explore (n-1)!
possible solutions to verify optimality.

### Algorithm 9: The "Verification" Procedure

The paper presents Algorithm 9 as the procedure for "checking the solution":

```
Algorithm 9: CheckSolution(TSP instance with n cities)
1. Generate all (n-1)! Hamiltonian cycles
2. Compute the cost of each cycle
3. Return the minimum cost cycle
4. If minimum cost ≤ budget, return "YES"
```

The paper claims this exponential procedure is the only way to "check the solution."

### The Lennard-Jones Problem

The paper also analyzes the Lennard-Jones cluster optimization problem as an example
of NP complexity, observing that finding the global minimum requires searching
through exponentially many configurations.

---

## Conclusion

From Proposition 6.12, the paper concludes:
1. Arbitrary NP problems (like GAP) cannot be verified in polynomial time
2. Therefore, NP problems cannot be in P
3. Therefore, P ≠ NP

---

## Why the Argument Fails

See [README.md](README.md) for a detailed analysis of the errors.

The core issue is that Algorithm 9 is a **solving** algorithm (finding the optimal
solution), not a **verification** algorithm (checking a given candidate solution).
The definition of NP requires polynomial-time verification of a given certificate,
not polynomial-time finding of the optimal solution.
