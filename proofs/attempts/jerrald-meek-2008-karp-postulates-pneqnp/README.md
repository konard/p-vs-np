# Jerrald Meek (2008) - Karp Postulates P!=NP Attempt

**Attempt ID**: 46 (from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm))
**Author**: Jerrald Meek
**Year**: 2008
**Claim**: P != NP
**Paper**: "Analysis of the postulates produced by Karp's Theorem" - [arXiv:0808.3222](https://arxiv.org/abs/0808.3222)
**Status**: arXiv preprint, final article in a four-article series

## Overview

This directory covers Woeginger live entry #46, which is distinct from
[`jerrald-meek-2008-pneqnp`](../jerrald-meek-2008-pneqnp/). Entry #43 is Meek's
earlier paper "P is a proper subset of NP"; entry #46 is the later paper
"Analysis of the postulates produced by Karp's Theorem".

Meek's fourth article argues that:

1. Karp reductions show that a polynomial-time SAT algorithm would solve every
   NP-complete problem in polynomial time.
2. A polynomial-time algorithm for one NP-complete problem supposedly would not
   necessarily produce a polynomial-time SAT algorithm.
3. Some special forms of Knapsack, such as base conversion, allegedly are
   NP-complete while also having polynomial-time algorithms.
4. These examples are used to challenge the usual interpretation of
   NP-completeness and conclude P != NP.

## Critical Errors

### 1. Reverses the Direction Needed for NP-Completeness

Showing that a polynomial-time problem is a special case of Knapsack does not
make that special case NP-complete. To prove a language `L` is NP-complete, SAT
or another NP-complete problem must reduce to `L`, not merely from `L` into a
known NP-complete problem.

### 2. Confuses Algorithms with Constructive Inversion of Reductions

If `L` is NP-complete and `L` is in P, then SAT is in P because SAT many-one
reduces to `L`. The proof does not require a discovered `L` algorithm to expose
an internal SAT-solving mechanism. Composition of the known reduction with the
`L` solver is enough.

### 3. Uses Nonstandard "Underlying K-SAT" Assumptions

The paper treats each NP-complete instance as though it has a unique underlying
K-SAT input relation that must be recovered or selected. Standard many-one
reductions do not require such a reconstruction; they require only that the
answer be preserved by a polynomial-time transformation.

### 4. Depends on Earlier Invalid Theorems

The conclusion imports the "Optimization", "Partition", and Knapsack theorems
from Meek's earlier articles. Those assumptions already require the invalid
search-space and partition arguments documented in entry #43.

### 5. Exhausts a False Algorithm Taxonomy

The final conclusion considers only search, partitioned search, direct
problem-form solutions, and "magical" solutions. This is not a theorem about
all deterministic algorithms, so it cannot prove a lower bound for SAT or any
NP-complete problem.

## Folder Structure

```
jerrald-meek-2008-karp-postulates-pneqnp/
├── README.md
├── ORIGINAL.pdf
├── ORIGINAL.md
├── proof/
│   ├── README.md
│   ├── lean/MeekKarpPostulatesProof.lean
│   └── rocq/MeekKarpPostulatesProof.v
└── refutation/
    ├── README.md
    ├── lean/MeekKarpPostulatesRefutation.lean
    └── rocq/MeekKarpPostulatesRefutation.v
```

## Key Formalization Results

The formalizations record the standard reduction fact that Meek's argument
rejects: if SAT polynomial-time many-one reduces to a language `L`, and `L` has a
polynomial-time decider, then SAT has a polynomial-time decider by composing the
reduction and the decider.

They also isolate the invalid inference that a special case of an NP-complete
problem is itself NP-complete.

## References

1. Meek, J. (2008). "Analysis of the postulates produced by Karp's Theorem",
   arXiv:0808.3222v5.
2. Meek, J. (2008). "P is a proper subset of NP", arXiv:0804.1079v12.
3. Karp, R. M. (1972). "Reducibility among combinatorial problems".
4. Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

**Status**: Refutation formalization complete; forward proof marked
unformalizable because the central NP-completeness and reduction claims are not
valid.
