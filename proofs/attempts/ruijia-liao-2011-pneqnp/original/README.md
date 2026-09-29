# Ruijia Liao (2011) - Original Materials

## Overview

This folder contains the original arXiv draft and the English reconstruction
of Ruijia Liao's 2011 attempt to prove P ≠ NP via 3SAT_N, aggressive truth
assignments, and a Cantor-style diagonal argument.

## Core Idea

The paper argues that:

1. 3SAT_N is NP-complete.
2. Aggressive truth assignments and their compositions form a metric space.
3. Regular Cauchy sequences of these compositions correspond to polynomial-time algorithm representations.
4. A diagonal argument on equivalence classes of such sequences should produce uncountably many algorithms, contradicting the countability of algorithms.

The refutation in the parent directory explains why Proposition 2 undermines the diagonal step.

## Reconstruction Files

- [`ORIGINAL.md`](ORIGINAL.md) - English reconstruction of the draft paper
- [`ORIGINAL.pdf`](ORIGINAL.pdf) - Original arXiv draft

## Related Material

- [`../README.md`](../README.md) - Full attempt analysis and error explanation
- [`../proof/README.md`](../proof/README.md) - Forward formalization
- [`../refutation/README.md`](../refutation/README.md) - Formal refutation
