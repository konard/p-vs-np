# Non-Orthodox Combinatorial Models Based on Discordant Structures

**Author**: Vladimir F. Romanov
**arXiv**: 1011.3944v2
**Claim**: P = NP via a polynomial-time 3-SAT algorithm

## Paper Outline

Romanov represents a 3-CNF formula as a table whose rows encode forbidden
triples of Boolean values. A formula whose variables appear in adjacent triples
under a fixed permutation is converted into a compact triplets structure (CTS).
Each tier of a CTS contains allowed binary triples for adjacent variables, and a
clearing procedure removes locally incompatible rows.

For an arbitrary 3-CNF formula, the paper decomposes clauses into several CTS
using different permutations of variables. These are called discordant
structures. The remaining task is to decide whether the discordant structures
have a joint satisfying set, meaning one Boolean assignment represented by all
structures.

The paper introduces hyperstructures and a systemic effective procedure (SEP) to
test this joint-existence condition without enumerating represented assignments.
Theorem 2 states that joint satisfying sets exist if and only if SEP forms a
non-empty hyperstructure system. Section 6 estimates the algorithm as
polynomial, `O(n^4 m)`.

## Critical Gap

The proof of Theorem 2 does not justify the step from a non-empty SEP result to a
global satisfying assignment. The construction maintains local compatibility
between compact triples, substructures, and same-name intersections. Such local
compatibility is not enough, by itself, to imply global satisfiability of a
constraint system.

The missing proof obligation is:

> Every non-empty hyperstructure produced by SEP contains a joint satisfying set
> for all discordant CTS, and therefore a satisfying assignment for the original
> 3-CNF formula.

Romanov's induction describes how local same-name intersections are propagated,
but it does not establish that the propagated representation is exact rather than
a relaxation containing spurious locally compatible components.

