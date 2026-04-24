# Sergey Kardash (2011) - Original Proof Idea

## Overview

Sergey Kardash's 2011 draft paper proposes the "pair cleaning" method for
k-SAT. The claim is that by grouping clauses into overlapping clause
combinations and repeatedly removing inconsistent rows from their value
tables, one can decide satisfiability in polynomial time.

For 3-SAT, the paper states an O(n^12) runtime. If the claim were correct, it
would imply P = NP because 3-SAT is NP-complete.

## Core Idea

The method is built from four main pieces:

1. **Clause groups** - clauses are grouped by the same set of k variable
   indices.
2. **Clause combinations** - each combination contains k+1 clause groups.
3. **Relationship structure** - the set of all such combinations.
4. **Pair cleaning** - repeatedly delete rows that have no compatible row in
   an overlapping combination.

The paper claims that the cleaned structure is non-empty if and only if the
original k-CNF formula is satisfiable.

## Claimed Complexity

The author bounds:

- the number of rows in each clause-group table,
- the number of rows in each clause-combination table,
- the number of clause combinations in the relationship structure, and
- the number of pairwise cleaning passes.

From those bounds, the paper concludes polynomial time O(n^{3(k+1)}), or
O(n^12) when k = 3.

## Reconstruction Files

- [`ORIGINAL.md`](ORIGINAL.md) - English reconstruction of the draft paper
- [`ORIGINAL.pdf`](ORIGINAL.pdf) - Original arXiv draft

## Related Material

- [`../README.md`](../README.md) - Overview and error analysis for the attempt
- [`../proof/README.md`](../proof/README.md) - Forward formalization
- [`../refutation/README.md`](../refutation/README.md) - Refutation and gap analysis
