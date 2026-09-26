# Gubin 2010 proof obligations

The Lean and Rocq files give an abstract specification of the claimed
tour/vertex correspondence. They do not construct Gubin's LP or prove P = NP.

The previous versions called a record containing only `numVars` and
`numConstraints` a linear program, declared every order to be a valid tour,
declared every feasible point to be a vertex, and asserted asymmetry and
integrality correspondence as axioms. The final P = NP step was admitted.
Those claims have been removed.

An actual forward formalization needs the paper's inequalities and projection
map, an exact ATSP tour predicate, objective preservation, and a proved
complexity reduction. The abstract `HasCorrespondence` predicate records two
necessary directions of the correspondence without asserting that Gubin's
construction satisfies them.

The [six-vertex refutation](../refutation/README.md) separately checks the
paper's equations (1.8) and (1.9) against a graph with no Hamiltonian tour.

See the [refutation audit](../refutation/README.md) for the concrete LP
counterexample and the separate illustrative examples.
