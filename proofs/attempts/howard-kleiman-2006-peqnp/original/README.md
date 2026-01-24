# Howard Kleiman (2006) - Original Proof Idea

## Overview

Howard Kleiman's December 2006 paper claims to prove **P = NP** by presenting a polynomial-time algorithm for the Asymmetric Traveling Salesman Problem (ATSP) using a modified Floyd-Warshall algorithm.

## The Claim

Kleiman asserted: "I present an exact algorithm for solving the ATSP in polynomial time."

If correct, since ATSP is NP-hard, this would prove that P = NP.

## Core Approach: Modified Floyd-Warshall for ATSP

### The Idea

Kleiman proposed:
1. **Matrix Transformation**: Transform an n×n asymmetric cost matrix M(a) into a 2n×2n symmetric cost matrix M(s)
2. **Apply Floyd-Warshall**: Run a modified Floyd-Warshall algorithm on M(s)
3. **Tour Extraction**: Extract an optimal ATSP tour from the result
4. **Polynomial Complexity**: The algorithm runs in O(n⁴) time

### The Mathematical Framework

Building on work by Jonker and Volgenannt (1986), the transformation creates a symmetric matrix M(s) from asymmetric matrix M(a) such that:
- M(s) has special structural properties
- Tours in M(s) correspond to tours in M(a)
- The transformation is polynomial time (O(n²))

### The Algorithm Steps

1. **Input**: Asymmetric n×n cost matrix M(a)
2. **Transform**: Create 2n×2n symmetric matrix M(s)
3. **Compute**: Apply modified Floyd-Warshall to M(s)
4. **Extract**: Obtain optimal tour in M(a) from M(s) solution
5. **Output**: Optimal ATSP tour

### Claimed Complexity

- **Transformation**: O(n²)
- **Floyd-Warshall**: O(n³) for standard, O(n⁴) for modified version
- **Extraction**: O(n²)
- **Total**: O(n⁴) - polynomial time

### Why This Would Prove P = NP

If the algorithm were correct:
- ATSP can be solved in polynomial time (O(n⁴))
- ATSP is NP-hard (Karp 1972)
- Therefore, all NP problems can be solved in polynomial time
- This implies P = NP

## The Central Assumption

The proof relies on the claim that:

> "Due to the special structure of M(s), an optimal tour in M(s) yields an optimal tour in M(a), and this can be found using a modified Floyd-Warshall algorithm in polynomial time."

## Why This Approach Is Appealing

The approach is attractive because:
- Floyd-Warshall is a well-established polynomial algorithm
- It efficiently solves shortest-path problems
- Matrix transformations can sometimes preserve problem structure
- The ATSP is superficially related to shortest paths

## Historical Context

This is one of several attempts by Kleiman to solve TSP variants:
- 2001: "The Floyd-Warshall Algorithm, the AP and the TSP"
- 2005: "The Symmetric Traveling Salesman Problem"
- 2006: "The Asymmetric Traveling Salesman Problem" (this attempt)
- 2011: "The General Traveling Salesman Problem"

## References

### Original Paper
- **Kleiman, H.** (2006). "The Asymmetric Traveling Salesman Problem"
  - arXiv:math.CO/0612114
  - Submitted: December 5, 2006
  - Last revised: December 9, 2006
  - Available at: http://arxiv.org/abs/math.CO/0612114

### Background Work
- **Jonker, R., & Volgenannt, A.** (1986). "Transforming asymmetric into symmetric traveling salesman problems"
- **Floyd, R. W.** (1962). "Algorithm 97: Shortest path"
- **Warshall, S.** (1962). "A theorem on boolean matrices"

### Context
- **Woeginger's P vs NP List**: Entry #37
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Karp, R. M.** (1972). "Reducibility among combinatorial problems"
