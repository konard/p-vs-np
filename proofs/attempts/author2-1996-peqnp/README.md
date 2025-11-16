# Plotnikov (1996) - P=NP Attempt

**Attempt ID**: 2
**Author**: Anatoly D. Plotnikov
**Year**: 1996
**Claim**: P=NP
**Journal**: SouthWest Journal of Pure and Applied Mathematics (SWJPAM), Volume 1, pp. 16-29
**Paper Title**: "Polynomial-Time Partition of a Graph into Cliques"

## Summary

This proof attempt claims to solve an NP-hard graph problem (the clique partition problem) in polynomial time, which would imply P=NP. The author presents an algorithm that purportedly partitions an arbitrary undirected graph into the minimum number of cliques in O(n⁵) time, where n is the number of vertices.

## The Main Argument

### The Clique Partition Problem

The **clique partition problem** (also known as the clique cover problem) asks: Given a graph G, partition its vertices into the minimum number of cliques (complete subgraphs). This problem is known to be NP-complete.

**Key Facts**:
- A clique is a subset of vertices where every pair is connected by an edge
- The clique partition problem is equivalent to graph coloring on the complement graph
- Finding the minimum number of cliques is NP-hard
- The decision version ("Can G be partitioned into ≤ k cliques?") is NP-complete

### Plotnikov's Approach

According to the abstract, Plotnikov claims to:
1. Use properties of finite partially ordered sets (posets)
2. Design an algorithm that runs in O(n⁵) time
3. Find the minimum clique partition for any undirected graph

If this algorithm is correct, it would solve an NP-complete problem in polynomial time, proving P=NP.

## The Error in the Proof

The fundamental issue with this proof attempt (as with many P=NP claims) is that it claims to solve an NP-complete problem in polynomial time without addressing why this contradicts decades of failed attempts and known theoretical barriers.

### Likely Sources of Error

Based on the nature of the clique partition problem, the error likely falls into one of these categories:

1. **Incomplete Algorithm**: The algorithm may not handle all graph structures correctly
   - May work for special cases (e.g., perfect graphs where this is solvable in polynomial time)
   - May fail on general graphs with complex structure

2. **Hidden Exponential Complexity**: The claimed O(n⁵) time may hide exponential operations
   - Subroutines may have exponential worst-case behavior
   - The partially ordered set construction may grow exponentially

3. **Incorrect Reduction or Problem Definition**:
   - May be solving a different (easier) problem
   - May be finding a clique partition, but not necessarily the minimum one
   - May confuse clique partition with related but easier problems

4. **Gap in Correctness Proof**:
   - The algorithm may be polynomial-time but incorrect
   - May produce suboptimal solutions that are not minimum clique partitions

### Why This Problem is Hard

The clique partition problem remains NP-complete because:
- It's equivalent to graph coloring on the complement graph (NP-complete)
- Reduction from other NP-complete problems (e.g., 3-SAT)
- No polynomial-time algorithm is known despite extensive research
- Remains hard even on restricted graph classes (e.g., cubic planar graphs)

## Formalization Strategy

Our formalization approach:

1. **Define the clique partition problem formally**
2. **Model Plotnikov's algorithm** (as much as can be reconstructed)
3. **Identify the gap** by attempting to prove:
   - Correctness: Does it always find the minimum?
   - Polynomial-time: Is it truly O(n⁵)?
4. **Document where the proof breaks down**

## Known Refutation

While there is no published explicit refutation of Plotnikov's specific paper, the claim contradicts:
- The widespread belief that P ≠ NP
- Decades of failed attempts to solve NP-complete problems in polynomial time
- The absence of verification by the theoretical computer science community
- The fact that if this were correct, it would have won the Clay Millennium Prize

The paper appeared in an electronic journal but was never validated or accepted by the mainstream complexity theory community.

## References

1. **Woeginger's P-versus-NP page**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #2)
2. **Semantic Scholar**: Corpus ID 202143792
3. **Clique Cover Problem**: Known to be NP-complete (Karp, 1972)
4. **Original Paper**: SouthWest Journal of Pure and Applied Mathematics, Volume 1, 1996, pp. 16-29

## Directory Structure

```
author2-1996-peqnp/
├── README.md (this file)
├── coq/
│   └── PlotnikovAttempt.v
├── lean/
│   └── PlotnikovAttempt.lean
└── isabelle/
    └── PlotnikovAttempt.thy
```

## Formalization Files

- `coq/PlotnikovAttempt.v` - Coq formalization
- `lean/PlotnikovAttempt.lean` - Lean 4 formalization
- `isabelle/PlotnikovAttempt.thy` - Isabelle/HOL formalization

Each formalization attempts to:
1. Define graphs and cliques formally
2. Define the clique partition problem
3. Model the claimed polynomial-time algorithm
4. Identify where the proof fails

## Status

This is a formalization of a failed P=NP proof attempt for educational purposes. The goal is to understand why such attempts fail and to develop formal verification skills.

---

*Part of the [P vs NP formal verification project](../../..)*
