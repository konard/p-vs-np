# Michael LaPlante (2015) - P=NP Attempt

**Navigation:** [Back to Repository Root](../../../README.md)

---

## Overview

**Attempt ID**: 102 (from Woeginger's list)
**Author**: Michael LaPlante
**Year**: 2015
**Claim**: P = NP
**Paper**: "A Polynomial Time Algorithm For Solving Clique Problems"
**arXiv**: [1503.04794](https://arxiv.org/abs/1503.04794)
**Refutation**: Cardenas et al., 2015 ([arXiv:1504.06890](https://arxiv.org/abs/1504.06890))

## Summary

In March 2015, Michael LaPlante claimed to prove P=NP by constructing a polynomial-time algorithm for the Clique Problem, which is known to be NP-complete. His paper presents "a single algorithm which solves the clique problems, 'What is the largest size clique?', 'What are all the maximal cliques?' and the decision problem, 'Does a clique of size k exist?' for any given graph in polynomial time."

## The Main Argument

### Claimed Approach

LaPlante's approach consists of two phases for solving the clique problem:

1. **Phase 1 - Triangle Enumeration**: For each vertex in the graph, find every 3-clique (triangle) containing it and list all vertices in each of these cliques.

2. **Phase 2 - Clique Extension**: Iterate through the list of 3-cliques to identify larger cliques by combining triangles that share common vertices.

The author claims this two-phase approach can solve:
- The k-clique decision problem (Does a clique of size k exist?)
- The k-clique enumeration problem (What are all cliques of size k?)
- The maximum clique problem (What is the largest clique?)

### The Clique Problem

The Clique Problem asks: Given an undirected graph G = (V, E) and an integer k, does G contain a clique of size at least k (i.e., a subset of k vertices where every pair is connected by an edge)?

This problem is NP-complete, proven by Karp in 1972.

### Why Polynomial Time for Clique Would Prove P=NP

The Clique Problem is one of Karp's 21 NP-complete problems. Since all NP-complete problems are polynomial-time reducible to each other, a polynomial-time algorithm for any NP-complete problem would imply polynomial-time algorithms for all problems in NP, thus proving P = NP.

## Known Refutation

In April 2015, Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, and Nathaniel S. Potrepka published a refutation titled "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" ([arXiv:1504.06890](https://arxiv.org/abs/1504.06890)).

The refutation paper analyzes both LaPlante's paper and a similar attempt by Tamta-Pande-Dhami, concluding that:

1. The algorithms presented in both papers are fundamentally flawed
2. Neither author successfully established that P = NP
3. The proposed algorithms fail to correctly solve the Clique Problem in general

## The Error in the Proof

Based on the refutation and fundamental complexity theory, the errors in LaPlante's attempt include:

### 1. Exponential Number of Maximal Cliques

A fundamental issue is that some graphs have exponentially many maximal cliques. The Moon-Moser graph family shows that an n-vertex graph can have up to 3^(n/3) maximal cliques. No algorithm that enumerates all maximal cliques can run in polynomial time on such graphs.

### 2. Failure of the Triangle-Based Approach

The approach of building larger cliques from triangles has several flaws:

- **Combinatorial Explosion**: The number of ways to combine triangles can grow exponentially
- **Correctness Issues**: Not all cliques can be correctly identified by simply merging triangles
- **Hidden Exponential Work**: The algorithm's analysis underestimates the work required in the extension phase

### 3. Incorrect Complexity Analysis

The paper claims polynomial-time complexity but fails to properly account for:

- The exponential number of clique candidates that may need to be checked
- The worst-case behavior on adversarial graph constructions
- The fundamental lower bounds known for the clique problem

### 4. Typical Pitfalls in Failed P=NP Attempts

This attempt exhibits common errors seen in many failed P=NP attempts:

- **Algorithm works on special cases but not general instances**: Many heuristics work well on specific problem structures but fail on the general case
- **Confusion between average-case and worst-case complexity**: An algorithm that works "often" is not sufficient
- **Missing polynomial-time bound verification**: Claims of polynomial time without rigorous proof of time complexity
- **Ignoring exponential barriers**: The fact that there can be exponentially many cliques means any algorithm that enumerates them cannot be polynomial-time

## Formalization Goal

The formal verification in this directory aims to:

1. **Formalize the Clique Problem** in Lean, Coq, and Isabelle
2. **Formalize what it means for an algorithm to solve the Clique Problem**
3. **Capture the claim**: If there exists a polynomial-time algorithm for Clique, then P = NP
4. **Identify the gap**: Show that any claimed algorithm must work on ALL instances (universal quantification)
5. **Demonstrate the failure mode**: Show that an algorithm working on only SOME instances is insufficient
6. **Highlight the exponential barrier**: Formalize that some graphs have exponentially many cliques

## Key Lessons

This attempt demonstrates several important principles:

1. **Universal vs. Existential Quantification**: Proving P=NP requires an algorithm that works for ALL instances, not just some instances
2. **Exponential Barriers Exist**: Some problems have inherent exponential structure (e.g., number of maximal cliques)
3. **Rigorous Verification is Essential**: Claims must be backed by formal proofs and comprehensive testing
4. **NP-Complete Problems are Hard**: There are deep reasons why these problems have resisted polynomial-time solutions for decades

## References

### Original Paper
- LaPlante, M. (2015). "A Polynomial Time Algorithm For Solving Clique Problems." arXiv:1503.04794 [cs.DS].

### Refutation
- Cardenas, H.A., Holtz, C., Janczak, M., Meyers, P., Potrepka, N.S. (2015). "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890 [cs.CC].

### Background on Clique Problem
- Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations, pp. 85-103.
- Moon, J.W., Moser, L. (1965). "On cliques in graphs." Israel Journal of Mathematics, 3(1):23-28.
- Garey, M.R., Johnson, D.S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness." W.H. Freeman.

### P vs NP Problem
- Cook, S.A. (1971). "The complexity of theorem-proving procedures." Proceedings of STOC.
- Clay Mathematics Institute: [P vs NP Official Problem Description](https://www.claymath.org/millennium/p-vs-np/)

## Formalization Structure

```
proofs/attempts/michael-laplante-2015-peqnp/
├── README.md                      (this file)
├── coq/
│   └── LaPlante2015.v            (Coq formalization)
├── lean/
│   └── LaPlante2015.lean         (Lean 4 formalization)
└── isabelle/
    ├── ROOT                       (Session configuration)
    └── LaPlante2015.thy          (Isabelle/HOL formalization)
```

## Status

- [ ] Documentation: Complete
- [ ] Lean formalization: In progress
- [ ] Coq formalization: In progress
- [ ] Isabelle formalization: In progress

---

**Note**: This formalization is for educational purposes to understand why certain approaches to P vs NP fail. The goal is to build intuition about the problem and common pitfalls in attempted proofs.
