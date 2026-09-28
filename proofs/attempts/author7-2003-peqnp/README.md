# Bolotashvili (2003) - P=NP via Linear Ordering Problem

**Attempt ID**: 7
**Author**: Givi Bolotashvili
**Year**: 2003
**Claim**: P = NP
**ArXiv ID**: cs.CC/0303008
**Status**: Unverified claim, not accepted by complexity theory community

## Overview

Givi Bolotashvili claimed to prove P=NP by presenting a polynomial-time algorithm for the Linear Ordering Problem (LOP), which is known to be NP-complete. If valid, such an algorithm would indeed prove P=NP, as solving any NP-complete problem in polynomial time implies all NP problems can be solved in polynomial time.

## Full Description

The paper titled "Solution of the Linear Ordering Problem (NP=P)" was archived on arXiv.org in March 2003. The abstract states: "A polynomial algorithm is obtained for the NP-complete linear ordering problem."

### Background: Linear Ordering Problem

The **Linear Ordering Problem (LOP)** is a classical NP-complete problem with the following definition:

- **Input**: A weighted directed complete graph (tournament) with n vertices
- **Goal**: Find a linear ordering (permutation) of the vertices that maximizes the sum of weights of edges going in the "forward" direction according to the ordering
- **Complexity**: Both MAX-LOP and MIN-LOP are NP-complete

The problem has many practical applications in:
- Graph drawing
- Triangulation of input-output matrices in economics
- Archeology (seriation)
- Ranking and aggregating preferences

### Earlier Version

An earlier version of this work appeared in 1990 in the journal "Soobshcheniya Akademii Nauk Gruzinskoi SSR" (Proceedings of the Georgian Academy of Sciences) under the title "A polynomial algorithm for a problem of linear orders." This version was written in Russian with English and Georgian summaries.

### Follow-up Work

Bolotashvili continued this line of research, publishing "Solving the Linear Ordering Problem Using the Facets (NP=P)" in the Bulletin of the Georgian National Academy of Sciences in 2023, suggesting ongoing work on polynomial-time approaches to this NP-complete problem.

## Main Argument/Approach

Based on the available information, the claimed approach involves:

1. **Facet-Based Algorithm**: The author proposes using facets of the linear ordering polytope to solve the problem in polynomial time
2. **Decomposition Strategy**: The linear ordering problem can be decomposed into components, some of which are tractable
3. **Claimed Polynomial Time**: The author asserts the algorithm runs in polynomial time for all instances

The technical details of the algorithm are not publicly available in sufficient detail to fully analyze the approach without access to the full paper.

## Known Issues and Likely Errors

While no formal published refutation exists for this specific paper, the claim is not accepted by the computational complexity community for several key reasons:

### 1. **Lack of Peer Review and Independent Verification**
- The paper was posted on arXiv but does not appear to have been published in a peer-reviewed venue
- No independent verification or replication of the claimed polynomial algorithm exists
- The result would be groundbreaking and would have received significant attention if valid

### 2. **Persistence of NP-Completeness Results**
- The Linear Ordering Problem remains classified as NP-complete in current literature
- Subsequent papers (2010s-2020s) continue to treat LOP as NP-hard and develop heuristic/approximation algorithms
- No polynomial-time exact algorithm is known or accepted for general LOP instances

### 3. **Common Pitfalls in P=NP Attempts**
Typical errors in claimed polynomial algorithms for NP-complete problems include:

- **Incomplete case analysis**: Algorithm may work for special cases but not all instances
- **Hidden exponential factors**: Algorithm may have polynomial number of steps, but each step requires exponential time or space
- **Incorrectness**: Algorithm may be polynomial but doesn't solve the problem correctly for all instances
- **Misunderstanding of problem statement**: Solving a restricted version that is actually in P

### 4. **The Facet Approach Issue**
The facet-based approach has a fundamental limitation:
- While facets of the linear ordering polytope are well-studied and useful for branch-and-cut algorithms
- Identifying which facet inequalities are violated for a given point can itself be an NP-hard problem
- Using facets for cutting planes doesn't guarantee polynomial-time solution to the full problem
- Branch-and-cut algorithms using facets are exact but exponential in worst case

### 5. **Decomposition Pitfall**
The claim about decomposing the problem into tractable components has issues:
- Research shows LOP can be expressed as sum of a P component and an NP-hard component
- However, the NP-hard component cannot be eliminated in the general case
- The hardness of the problem lies precisely in the irreducible NP-hard component

## Likely Error

The most probable error is one of the following:

1. **Hidden exponential complexity**: The algorithm may have polynomial number of iterations, but the work per iteration (e.g., solving subproblems, identifying violated facets) may require exponential time
2. **Incomplete correctness proof**: The algorithm may be polynomial but not correctly solve all instances of LOP
3. **Gap in case analysis**: The algorithm may handle many cases in polynomial time but miss exponentially many special cases

## Formalization Goal

The goal of this formalization is to:

1. Define the Linear Ordering Problem formally in Rocq, Lean, and Isabelle
2. Formalize the claim that a polynomial-time algorithm exists for LOP
3. Attempt to formalize the algorithm's structure based on available descriptions
4. Identify where the proof breaks down or where the polynomial-time guarantee fails
5. Document the specific gap or error in the proof

## Source References

- **Woeginger's P vs NP Page**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #7)
- **ArXiv Paper**: https://arxiv.org/abs/cs.CC/0303008
- **Parent Issue**: Part of [#44 - Test all P vs NP attempts formally](https://github.com/konard/p-vs-np/issues/44)
- **This Issue**: [#75 - Formalize: Unknown (2003) - P=NP](https://github.com/konard/p-vs-np/issues/75)

## Structure

This attempt formalization is organized as follows:

- `README.md` (this file) - Detailed description and analysis
- `rocq/` - Rocq formalization
  - `LinearOrdering.v` - LOP definition and properties
  - `Bolotashvili2003.v` - Attempted formalization of the claim
- `lean/` - Lean 4 formalization
  - `LinearOrdering.lean` - LOP definition and properties
  - `Bolotashvili2003.lean` - Attempted formalization of the claim
- `isabelle/` - Isabelle/HOL formalization
  - `LinearOrdering.thy` - LOP definition and properties
  - `Bolotashvili2003.thy` - Attempted formalization of the claim

## Status

This formalization is part of the educational repository for studying P vs NP attempts. The formalization captures the claim structure and identifies where gaps would occur in a complete proof.

---

**Note**: This is an educational formalization to understand common errors in P vs NP proof attempts. The original author's work represents a serious attempt to solve an important problem, and this analysis is conducted respectfully for educational purposes.
