# Formalization: Hanlin Liu (2014) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation)

---

## Metadata

- **Attempt ID**: 96 (from Woeginger's list)
- **Author**: Hanlin Liu
- **Year**: 2014
- **Claim**: P = NP
- **Method**: Polynomial-time algorithm for Hamiltonian Circuit Problem
- **Claimed Time Complexity**: O(|V|^9)
- **arXiv Link**: http://arxiv.org/abs/1401.6423
- **Status**: Withdrawn by author (October 31, 2018)

## Summary

In January 2014, Hanlin Liu claimed to establish P=NP by constructing a polynomial-time algorithm for the Hamiltonian circuit problem in a graph G=(V,E), with a claimed time complexity of O(|V|^9). The paper "A Algorithm for the Hamilton Circuit Problem" was initially submitted to arXiv but was later withdrawn by the author.

## Main Argument/Approach

Based on the available information from the arXiv abstract and metadata:

### Core Algorithm Idea

1. **Data Structure**: Uses a "multistage directed graph" to store all data related to the Hamiltonian Circuit
2. **Recursive Properties**: Implements an "exclusive method" to handle recursive properties
3. **Path Elimination**: Systematically deletes all paths that don't satisfy necessary and sufficient conditions for a Hamiltonian Circuit
4. **Completeness Claim**: The algorithm was intended to cover all cases and find a Hamiltonian Circuit (if it exists) in polynomial time

### Intended Approach

The algorithm appears to:
- Build a multi-stage graph representation
- Apply recursive filtering based on properties of Hamiltonian circuits
- Eliminate invalid paths at each stage
- Conclude with either a Hamiltonian circuit or proof of non-existence

### Why This Would Imply P = NP

The Hamiltonian Circuit Problem is a well-known NP-complete problem (proven by Karp, 1972). If a polynomial-time algorithm existed for it, then:
1. All NP problems could be reduced to Hamiltonian Circuit in polynomial time (by NP-completeness)
2. The composition of polynomial-time reductions and a polynomial-time algorithm remains polynomial
3. Therefore, all NP problems would be solvable in polynomial time
4. This would establish P = NP

## Known Refutation

### Author's Own Admission

The paper was **withdrawn by the author** with the following statement in the arXiv comments:

> "Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt"

### The Error in the Proof

Based on the author's withdrawal comments and abstract:

1. **Incomplete Coverage**: The algorithm does not handle all possible cases of the Hamiltonian Circuit Problem
2. **Insufficient Generality**: The abstract itself admits the algorithm only "covers some cases of Hamilton Circuit Problem"
3. **Gap in Reasoning**: The claim that the path elimination method would systematically find all Hamiltonian circuits in polynomial time was not substantiated

### Why the Approach Failed

The fundamental error appears to be:

- **Overestimation of Completeness**: The author believed the recursive property elimination would be exhaustive, but it was not
- **Case Coverage Gap**: There exist graph structures where the proposed algorithm either:
  - Fails to find an existing Hamiltonian circuit, or
  - Takes exponential time to verify all cases
- **NP-Complete Hardness**: The Hamiltonian Circuit Problem's NP-completeness implies that any polynomial-time algorithm would need to overcome fundamental complexity barriers—the proposed algorithm did not achieve this

### Historical Context

This attempt joins hundreds of similar failed attempts to prove P=NP by:
1. Designing a seemingly clever algorithm for an NP-complete problem
2. Underestimating the difficulty of worst-case instances
3. Having incomplete coverage of all possible cases
4. Failing to account for the exponential blow-up in hard instances

## Formalization Strategy

Since the paper PDF is not available (404 error when attempting to download) and was withdrawn, our formalization will focus on:

### What We Can Formalize

1. **The Hamiltonian Circuit Problem Definition**: Formal specification of the problem
2. **The Claim Structure**: What it would mean to have a polynomial-time algorithm for HC
3. **The Implication**: Proof that polynomial-time HC algorithm implies P=NP
4. **The Incompleteness**: A framework showing that any incomplete algorithm cannot solve an NP-complete problem

### What We Cannot Formalize

1. **The Specific Algorithm**: Without the paper PDF, we cannot access the exact algorithmic details
2. **The Precise Error**: We can only work from the author's admission of incompleteness

### Our Approach

We will formalize:
- The Hamiltonian Circuit Problem as a decision problem
- The concept of a polynomial-time algorithm
- The reduction from HC to establish P=NP
- A meta-theorem about incomplete algorithms
- A placeholder for the specific algorithm (with comments explaining the gap)

## Formalizations

This directory contains formalizations in three proof assistants:

- **[Lean 4](lean/)** - `lean/HanlinLiu2014.lean`
- **[Coq](coq/)** - `coq/HanlinLiu2014.v`
- **[Isabelle/HOL](isabelle/)** - `isabelle/HanlinLiu2014.thy`

Each formalization:
1. Defines the Hamiltonian Circuit Problem
2. States the claim that a polynomial-time algorithm exists
3. Proves that such an algorithm would imply P=NP
4. Documents the incompleteness error

## Key Insights

### Why This Type of Error is Common

Many attempted P=NP proofs via algorithms for NP-complete problems fail because:

1. **Hard Instances Are Not Obvious**: Worst-case hard instances for NP-complete problems are subtle
2. **Polynomial vs Exponential Boundary**: It's easy to design algorithms that work on many cases but fail or become exponential on hard cases
3. **Verification Burden**: Proving an algorithm works on *all* instances requires rigorous mathematical proof
4. **Complexity Barriers**: Natural proofs barrier (Razborov-Rudich) suggests that many "natural" algorithmic approaches will fail

### Educational Value

This formalization demonstrates:
- How to properly specify NP-complete problems
- The structure of reduction-based P=NP arguments
- The importance of completeness proofs for algorithms
- Why informal algorithmic descriptions are insufficient for resolving P vs NP

## References

### This Attempt
- **arXiv**: [1401.6423](http://arxiv.org/abs/1401.6423) - A Algorithm for the Hamilton Circuit Problem (withdrawn)
- **Woeginger's List**: Entry #96 on https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Hamiltonian Circuit Problem
- **Karp, R.M.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, pp. 85-103.

### P vs NP Background
- **Cook, S.** (1971). "The complexity of theorem-proving procedures." *STOC*
- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach*

### Barrier Results
- **Razborov, A., Rudich, S.** (1997). "Natural Proofs." *J. Comput. System Sci.*

## Status

- ✅ README.md: Complete
- 🚧 Lean formalization: In progress
- 🚧 Coq formalization: In progress
- 🚧 Isabelle formalization: In progress

---

**Note**: This formalization is for educational purposes, demonstrating how to analyze and formalize failed proof attempts. The author (Hanlin Liu) has explicitly acknowledged the error and withdrawn the paper, showing proper scientific integrity.

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../../P_VS_NP_TASK_DESCRIPTION.md) | [All Proof Frameworks](../../../README.md#-formal-verification)
