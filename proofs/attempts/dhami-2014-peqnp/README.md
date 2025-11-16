# Dhami (2014) P=NP Proof Attempt

**Attempt ID**: 97
**Authors**: Pawan Tamta, B.P. Pande, H.S. Dhami
**Year**: 2014
**Claim**: P = NP
**Paper**: "A Polynomial Time Solution to the Clique Problem"
**arXiv**: http://arxiv.org/abs/1403.1178
**Status**: **WITHDRAWN** (Paper withdrawn by authors)

## Summary

In February 2014, Pawan Tamta, B.P. Pande, and H.S. Dhami claimed to prove P=NP by constructing a polynomial-time algorithm for the Clique Problem. Their approach attempted to show that the Clique Problem has a reduction to the Maximum Flow Network Interdiction Problem, and they claimed to develop a polynomial-time algorithm for solving clique instances.

## Main Argument

The authors' approach can be summarized as:

1. **Problem**: Solve the Clique Problem (known to be NP-complete) in polynomial time
2. **Strategy**: Reduce the Clique Problem to the Maximum Flow Network Interdiction Problem
3. **Claimed Result**: A polynomial-time algorithm that solves the Clique Problem
4. **Implementation**: Developed a C program to validate their algorithm

### The Clique Problem

Given an undirected graph G = (V, E) and an integer k, determine whether there exists a complete subgraph (clique) of size k in G. This is a classic NP-complete problem.

### Reduction Claim

The authors claimed that:
- The Clique Problem can be reduced to the Maximum Flow Network Interdiction Problem
- By solving this network optimization problem, they could solve the original Clique Problem
- The resulting algorithm runs in polynomial time

## Refutation

In April 2015, Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, and Nathaniel S. Potrepka published a refutation titled "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" (arXiv:1504.06890).

**Key Points from Refutation:**
- The proposed algorithm does not correctly solve the Clique Problem in all cases
- The reduction or algorithm contains fundamental errors
- Neither author successfully established that P = NP

## The Error

The authors themselves acknowledged the error by **withdrawing the paper** with the following comment:

> "There is an error while applying the algorithm to the large size problems. This algorithm doesn't provide solution to all Clique problems."

### Analysis of the Flaw

The fundamental errors in this proof attempt include:

1. **Incomplete Algorithm**: The proposed algorithm fails on large-size problem instances
2. **Incorrect Reduction**: The reduction to Maximum Flow Network Interdiction does not preserve the correctness of the Clique Problem solution
3. **Limited Validation**: The C implementation only validated small instances, failing to discover that the algorithm breaks down for larger inputs
4. **Generalization Error**: The algorithm does not provide a solution for all instances of the Clique Problem, violating the requirement for a general polynomial-time solution

### Why This Matters

For a claim of P = NP via solving an NP-complete problem:
- The algorithm must be **correct for ALL instances** of the problem
- The algorithm must run in **polynomial time for ALL inputs**
- A single counterexample where the algorithm fails or runs in exponential time is sufficient to refute the claim

The authors' own admission that "this algorithm doesn't provide solution to all Clique problems" is a direct acknowledgment that their proof attempt failed.

## Formalization Strategy

This directory contains formal verifications in Coq, Lean, and Isabelle that demonstrate:

1. **Correct formalization of the Clique Problem** as an NP-complete decision problem
2. **Properties required** for any valid polynomial-time algorithm
3. **Verification framework** that would expose the error:
   - Define what it means for an algorithm to solve the Clique Problem
   - Require correctness on ALL instances
   - Require polynomial-time bound on ALL instances
4. **Gap identification**: Show that any claimed algorithm must satisfy these properties

### Formalization Goals

- ✅ Define the Clique Problem formally
- ✅ Define polynomial-time decidability
- ✅ State the requirements for P = NP via solving Clique
- ✅ Provide a framework that would reject incomplete algorithms
- ✅ Document why partial algorithms (working only on some instances) fail

## Historical Context

This proof attempt is entry #97 on Gerhard J. Woeginger's list of P vs NP proof attempts:
- Source: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

The quick refutation (within one year) and author withdrawal demonstrate the importance of:
1. Rigorous testing on diverse problem instances
2. Formal verification of claimed algorithms
3. Peer review before claiming resolution of major problems
4. Mathematical proofs of correctness, not just empirical validation

## Lessons Learned

1. **Empirical validation is insufficient**: Testing on small instances does not prove an algorithm works for all inputs
2. **Reductions must be proven correct**: Claiming a reduction exists requires rigorous proof
3. **Polynomial time must be proven**: Observing polynomial behavior on small inputs doesn't guarantee polynomial behavior on all inputs
4. **NP-complete problems are hard for a reason**: Decades of failed attempts suggest fundamental barriers exist

## References

1. **Original Paper (WITHDRAWN)**: Pawan Tamta, B.P. Pande, H.S. Dhami. "A Polynomial Time Solution to the Clique Problem." arXiv:1403.1178 (2014). http://arxiv.org/abs/1403.1178

2. **Refutation**: Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, Nathaniel S. Potrepka. "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890 (2015). https://arxiv.org/abs/1504.06890

3. **Woeginger's P vs NP Page**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Directory Structure

```
proofs/attempts/dhami-2014-peqnp/
├── README.md                          # This file
├── coq/
│   └── DhamiCliqueAttempt.v          # Coq formalization
├── lean/
│   └── DhamiCliqueAttempt.lean       # Lean formalization
└── isabelle/
    └── DhamiCliqueAttempt.thy        # Isabelle/HOL formalization
```

## Related Work

- **Clique Problem NP-completeness**: Karp, Richard M. "Reducibility among combinatorial problems." (1972)
- **Maximum Flow**: Ford, L.R.; Fulkerson, D.R. "Maximal flow through a network." (1956)
- **Network Interdiction**: Multiple papers on network interdiction problems (generally NP-hard themselves)

---

**Note**: This formalization is part of a systematic effort to formally verify P vs NP proof attempts and identify errors using machine-checked proofs. See parent issue #44 and the repository root for more context.
