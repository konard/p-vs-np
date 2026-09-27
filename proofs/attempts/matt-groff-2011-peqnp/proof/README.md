# Groff (2011): forward proof sketch

The [Lean](lean/GroffProof.lean) and [Rocq](rocq/GroffProof.v) files outline
the paper's clause-polynomial construction, coefficient transformations,
finite-field equations, and claimed runtime. Unproved premises and
placeholders are obligations, not verified facts about the algorithm.

A complete proof needs a representation and bit-cost analysis for every
operation, correctness of the reconstruction from the evaluated field
values, and a precise treatment of the stated error probability. The
[refutation audit](../refutation/README.md) proves a collision for one
raw polynomial evaluation on actual 3-CNF inputs. It does not model the
later transformations or settle those obligations.
