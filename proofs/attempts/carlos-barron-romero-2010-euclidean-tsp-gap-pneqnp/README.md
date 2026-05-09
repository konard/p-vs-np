# Carlos Barron-Romero (2010) - P≠NP via E2DTSP versus GAP

**Attempt ID**: 69 (from Woeginger's list)
**Author**: Carlos Barron-Romero
**Year**: 2010
**Claim**: P ≠ NP
**Status**: Refuted
**Source**: arXiv:1101.0160

## Summary

This directory formalizes Carlos Barron-Romero's December 2010 paper
"The Complexity of Euclidian 2 Dimension Travelling Salesman Problem
versus General Assign Problem, NP is not P." The paper compares Euclidean
two-dimensional TSP (E2DTSP) with the General Assign Problem (GAP). It
argues that E2DTSP has geometric triangle-reduction structure, while
arbitrary GAP instances do not preserve such structure. From this
contrast, the paper concludes that arbitrary hard NP problems do not have
polynomial-time algorithms and hence P is not NP.

This is a distinct Woeginger entry from the repository's existing
`carlos-barron-romero-2010-pneqnp` directory. That older directory
matches entry #62, "The Complexity Of The NP-Class"; this one matches
entry #69 and arXiv:1101.0160.

## Main Argument

The paper's intended chain is:

1. E2DTSP is a special case of GAP whose edge weights come from points in
   the Euclidean plane.
2. Euclidean distances satisfy the triangle inequality, so E2DTSP is
   claimed to be "triangle reducible."
3. Arbitrary GAP instances can have random edge weights and need not
   preserve any geometric or inherited reduction property.
4. Therefore a large arbitrary GAP has no polynomial-time algorithm for
   verifying or solving its solution.
5. Since GAP represents hard NP problems, P is not NP.

## The Error

The proof does not establish a complexity lower bound. The absence of the
specific triangle-reduction property used for E2DTSP does not imply the
absence of every possible polynomial-time algorithm for GAP or for any
NP-complete decision problem.

The argument also mixes several different tasks:

- verifying a proposed tour or certificate,
- proving that a proposed solution is globally optimal,
- solving an optimization problem, and
- separating P from NP for decision languages.

For NP, verification means checking a given certificate in polynomial time.
For the decision version of TSP, a certificate is a tour whose cost is at
most the given bound; checking that certificate is polynomial. Proving
optimality of an optimization solution is a different and generally harder
task.

The formalization records the valid local observations as assumptions,
then isolates the unsupported step:

> no triangle-reduction property for arbitrary GAP -> no polynomial-time
> algorithm for GAP.

That implication is exactly what would need proof. It is not supplied by
the paper, and it does not follow from the preceding propositions.

## Formalization Contents

- `original/` contains the downloaded arXiv PDF, the TeX source, a
  markdown reconstruction, and a short source summary.
- `proof/` follows the original proof attempt and marks the missing
  lower-bound implication as the point where formalization cannot proceed.
- `refutation/` gives a formal counter-analysis: lack of one structural
  property cannot prove lack of every polynomial-time algorithm.

## References

- Barron-Romero, Carlos. "The Complexity of Euclidian 2 Dimension
  Travelling Salesman Problem versus General Assign Problem, NP is not P."
  arXiv:1101.0160, submitted December 30, 2010.
- Woeginger's P versus NP page, entry #69.
- Papadimitriou, C. H. "The Euclidean travelling salesman problem is
  NP-complete." Theoretical Computer Science, 1977.
