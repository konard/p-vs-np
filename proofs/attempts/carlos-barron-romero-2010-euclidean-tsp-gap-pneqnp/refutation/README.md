# Refutation

The refutation formalizes the core logical flaw in the attempt.

The paper proves at most that arbitrary GAP instances need not inherit the
Euclidean triangle-reduction property. That statement is compatible with
the existence of some other polynomial-time algorithm. Therefore it cannot
entail P≠NP without an independent lower-bound theorem ruling out every
polynomial-time algorithm.

The formal files model this with a generic property `HasTriangleReduction`
and a generic complexity predicate `InP`. They prove that a countermodel is
consistent: a problem may lack triangle reduction and still be in P.
