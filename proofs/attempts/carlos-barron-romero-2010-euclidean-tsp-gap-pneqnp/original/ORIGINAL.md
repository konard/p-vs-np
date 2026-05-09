# The Complexity of Euclidian 2 Dimension Travelling Salesman Problem versus General Assign Problem, NP is not P

**Author**: Carlos Barron-Romero
**Year**: 2010
**Source**: arXiv:1101.0160v1
**Submitted**: December 30, 2010

## Abstract Reconstruction

The paper compares two NP problems: the Euclidean two-dimensional
Travelling Salesman Problem (E2DTSP) and the General Assign Problem
(GAP). It claims that E2DTSP has a triangle-reduction property that
allows polynomial-time verification of a solution, while arbitrary GAP
instances lack such structure. It presents this contrast as a solution to
the conjecture that NP is not P.

## Definitions

`GAP_n` is defined as a complete directed graph with vertex set `V_n`, a
cost function on ordered edges, and an objective function for evaluating
cycles. Solving a GAP means finding a cycle with minimum or maximum
objective value.

`E2DTSP_n` is defined as the special case where vertices are points in
the Euclidean plane, edge costs are Euclidean distances, the cost matrix
is symmetric and nonnegative, and the objective is the sum of the edge
costs in a Hamiltonian cycle.

## Main Propositions

The paper states that any `GAP_n` has a solution because its search space
of Hamiltonian cycles is finite. It also states that a general `GAP_n`
has `(n - 1)!` complete cycles.

It contrasts E2DTSP and GAP:

- For E2DTSP, path cost is monotonically increasing when a path is
  extended.
- For GAP, path cost need not be monotonically increasing.
- In E2DTSP, Euclidean geometry is claimed to support a triangle
  reduction that preserves the optimal tour.
- In arbitrary GAP, random edge values can destroy geometric or inherited
  structure.

The paper states that, given any E2DTSP instance, there exists a
triangulation preserving the solution. It then says that this is related
to the earlier proposition that E2DTSP has a polynomial-time algorithm to
verify the solution.

The central negative proposition is:

> Given an arbitrary and large `GAP_n`, it has no polynomial algorithm for
> verifying its solution.

The proof is given as immediate from a previous proposition saying that
combining a GAP instance with arbitrary random edges can destroy the
property used by a polynomial-time verifying algorithm for a smaller
instance.

## Conclusion Reconstruction

The paper concludes that E2DTSP represents a structured, tractable class,
while arbitrary GAP represents hard NP problems. Since arbitrary GAP is
claimed not to have a polynomial-time verification or solving algorithm
in the general worst case, the paper concludes that P is not NP.

## Formalization Boundary

The text can support formal statements that E2DTSP is a special case of
GAP and that the paper assumes a triangle-reduction property for E2DTSP.
It does not prove the universal lower-bound statement needed for P ≠ NP:

```text
NoTriangleReductionForGAP -> NotInP(GAP)
```

Lacking one particular structural property is not a proof that no
polynomial-time algorithm exists. The proof and refutation files isolate
that missing implication.
