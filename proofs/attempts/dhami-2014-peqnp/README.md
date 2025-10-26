# Dhami et al. (2014) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md)

---

## Overview

**Attempt ID**: 97 (from Woeginger's list)
**Authors**: Pawan Tamta, B.P. Pande, H.S. Dhami
**Year**: 2014
**Claim**: P = NP
**Paper**: "A Polynomial Time Solution to the Clique Problem"
**arXiv**: [1403.1178](https://arxiv.org/abs/1403.1178) (withdrawn)
**Refutation**: Cardenas et al., 2015 ([arXiv:1504.06890](https://arxiv.org/abs/1504.06890))

## Summary

In February 2014, Pawan Tamta, B.P. Pande, and H.S. Dhami claimed to prove P=NP by constructing a polynomial time algorithm for the Clique Problem, which is known to be NP-complete. Their approach was based on a reduction from the Clique Problem to the Maximum Flow Network Interdiction Problem.

**Status**: The paper was **withdrawn by the authors** themselves, with the explicit comment on arXiv stating:

> "There is an error while applying the algorithm to the large size problems. This algorithm doesn't provide solution to all Clique problems"

This admission by the authors themselves confirms that the proposed algorithm fails for certain problem instances.

## The Main Argument

### Claimed Approach

1. **Reduction Strategy**: The authors claim that the Clique Problem can be reduced to the Maximum Flow Network Interdiction Problem
2. **Algorithm Development**: They propose to develop a polynomial time algorithm based on this reduction
3. **Conclusion**: Since they claim a polynomial time algorithm for an NP-complete problem (Clique), they conclude P = NP

### The Clique Problem

The Clique Problem asks: Given an undirected graph G = (V, E) and an integer k, does G contain a clique of size at least k (i.e., a subset of k vertices where every pair is connected by an edge)?

This problem is NP-complete, proven by Karp in 1972.

### Maximum Flow Network Interdiction Problem

The Maximum Flow Network Interdiction Problem involves finding optimal ways to disrupt flow in a network by removing edges or reducing capacities, subject to budget constraints. Various versions of this problem have different complexity characterizations.

## Known Refutation

In April 2015, Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, and Nathaniel S. Potrepka published a refutation titled "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" ([arXiv:1504.06890](https://arxiv.org/abs/1504.06890)).

The refutation paper analyzes both the Dhami et al. paper and a similar attempt by LaPlante, concluding that:

1. The algorithms presented in both papers are fundamentally flawed
2. Neither author successfully established that P = NP
3. The proposed reductions and algorithms fail to correctly solve the Clique Problem in general

## The Error in the Proof

Based on the available evidence, the errors in this attempt include:

### 1. Incomplete Algorithm (Confirmed by Authors)

The authors themselves acknowledged in their arXiv comments that:
- The algorithm fails on large-size problems
- The algorithm does not provide solutions to all Clique problems

This is a **fundamental failure** - any claimed polynomial-time algorithm for an NP-complete problem must work for ALL instances, not just some subset.

### 2. Invalid or Incorrect Reduction

The reduction from the Clique Problem to the Maximum Flow Network Interdiction Problem appears to be either:
- Incorrectly formulated
- Not polynomial-time preserving
- Not equivalence-preserving (i.e., it doesn't maintain the yes/no answer)

### 3. Lack of Rigorous Proof

The paper lacks:
- Formal correctness proofs for the algorithm
- Rigorous complexity analysis
- Proof that the reduction preserves problem instances correctly
- Testing on comprehensive benchmark instances

### 4. Typical Pitfalls in Failed P=NP Attempts

This attempt exhibits common errors seen in many failed P=NP attempts:
- **Algorithm works on special cases but not general instances**: Many heuristics work well on specific problem structures but fail on the general case
- **Confusion between average-case and worst-case complexity**: An algorithm that works "often" is not sufficient
- **Missing polynomial-time bound verification**: Claims of polynomial time without rigorous proof of time complexity
- **Reduction errors**: Invalid problem transformations that don't preserve computational complexity

## Formalization Goal

The formal verification in this directory aims to:

1. **Formalize the Clique Problem** in Lean, Coq, and Isabelle
2. **Formalize what it means for an algorithm to solve the Clique Problem**
3. **Capture the claim**: If there exists a polynomial-time algorithm for Clique, then P = NP
4. **Identify the gap**: Show that any claimed algorithm must work on ALL instances (universal quantification)
5. **Demonstrate the failure mode**: Show that an algorithm working on only SOME instances is insufficient

## Key Lessons

This attempt demonstrates several important principles:

1. **Universal vs. Existential Quantification**: Proving P=NP requires an algorithm that works for ALL instances (∀), not just some instances (∃)
2. **Rigorous Verification is Essential**: Claims must be backed by formal proofs and comprehensive testing
3. **NP-Complete Problems are Hard**: There are deep reasons why these problems have resisted polynomial-time solutions for decades
4. **Reductions Must Preserve Complexity**: A reduction must work correctly AND preserve polynomial-time bounds in both directions

## References

### Original Paper
- Tamta, P., Pande, B.P., Dhami, H.S. (2014). "A Polynomial Time Solution to the Clique Problem." arXiv:1403.1178 [cs.CC]. **[Withdrawn]**

### Refutation
- Cardenas, H.A., Holtz, C., Janczak, M., Meyers, P., Potrepka, N.S. (2015). "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890 [cs.CC].

### Background on Clique Problem
- Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations, pp. 85-103.
- Garey, M.R., Johnson, D.S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness." W.H. Freeman.

### P vs NP Problem
- Cook, S.A. (1971). "The complexity of theorem-proving procedures." Proceedings of STOC.
- Clay Mathematics Institute: [P vs NP Official Problem Description](https://www.claymath.org/millennium/p-vs-np/)

## Formalization Structure

```
proofs/attempts/dhami-2014-peqnp/
├── README.md                    (this file)
├── coq/
│   └── DhamiAttempt.v          (Coq formalization)
├── lean/
│   └── DhamiAttempt.lean       (Lean 4 formalization)
└── isabelle/
    └── DhamiAttempt.thy        (Isabelle/HOL formalization)
```

## Status

- ✅ Documentation: Complete
- 🚧 Lean formalization: In progress
- 🚧 Coq formalization: In progress
- 🚧 Isabelle formalization: In progress

---

**Note**: This formalization is for educational purposes to understand why certain approaches to P vs NP fail. The goal is to build intuition about the problem and common pitfalls in attempted proofs.
