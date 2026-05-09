# Analysis of the Postulates Produced by Karp's Theorem

**Author**: Jerrald Meek
**arXiv ID**: 0808.3222v5
**Date**: August 2008 (version 5 submitted September 3, 2008)
**Source**: [arXiv:0808.3222](https://arxiv.org/abs/0808.3222)
**Woeginger Entry**: #46

This is a structured reconstruction and summary of Meek's fourth article in a
series on P vs NP. The original PDF is stored as `ORIGINAL.pdf`.

## Abstract

Meek claims that Karp's theorem supports only the direction from a
polynomial-time K-SAT solution to polynomial-time solutions for all NP-complete
problems. He argues that a polynomial-time solution to some NP-complete problem
does not necessarily produce a polynomial-time solution to all NP-complete
problems.

## Preliminaries

The paper assumes several earlier Meek results:

- the "P = NP Optimization Theorem";
- the "P = NP Partition Theorem";
- several Knapsack theorems about random sets, compositions, and qualities of
  set elements.

These imported theorems are central to the conclusion. They are also the same
style of unsupported search-space claims addressed in the entry #43
formalization for "P is a proper subset of NP".

## Claimed Postulates from Karp's Theorem

Meek separates the standard understanding of NP-completeness into two claims:

1. K-SAT can be reduced to any NP-complete problem, so a fast K-SAT solution
   would solve any NP-complete problem.
2. A fast solution to any NP-complete problem would produce a fast solution to
   the underlying K-SAT problem.

The paper accepts the first claim and rejects the second. The rejection is based
on an extra requirement that a solver for the target problem must somehow reveal
or solve an "underlying" K-SAT instance directly.

## Base Conversion and Knapsack

The paper then attempts to prove that converting a decimal number into a binary
number is a form of 0-1 Knapsack and therefore is NP-complete, while also being
solvable in deterministic polynomial time.

The key error is directional. A polynomial-time special case of an NP-complete
problem is not thereby NP-complete. To prove base conversion NP-complete, one
would need a polynomial-time many-one reduction from SAT or another known
NP-complete problem to base conversion.

## K-SAT Input Relation Theorem

Meek argues that an algorithm relying on the form of one NP-complete problem or
on special qualities of its inputs will not transfer to all other NP-complete
problems. This misses the standard composition argument: if SAT reduces to `L`
and `L` is in P, then SAT is in P by transforming SAT instances into `L`
instances and running the `L` decider.

## Conclusion Claimed by the Paper

The article concludes that P != NP after classifying possible algorithms into
search, partitioned search, direct special-form solutions, and "magical"
solutions. This classification is not an exhaustive formal model of deterministic
computation and does not establish a lower bound.

## Formalization Notes

The accompanying Lean and Rocq files do not formalize Meek's claimed proof as a
valid theorem. Instead they formalize the standard reduction composition fact and
pinpoint why the claimed counterexample to Karp-style reasoning does not follow.
