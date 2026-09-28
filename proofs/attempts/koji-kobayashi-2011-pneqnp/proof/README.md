# Forward Proof Attempt

This folder formalizes Kobayashi's 2011 argument in the direction intended by
the paper.

The Lean and Rocq files introduce abstract predicates for membership in the
classes `NP`, `AL`, `P`, `NC`, `NL`, and `L`, then name the four constructed
languages:

- `CHAOS`,
- `ORDER`,
- `LAYER`,
- `TWINE`.

The formalization keeps the claimed membership results and the claimed lower
bounds as separate assumptions. That separation is important: the paper's
actual gap is not in the final chaining argument, but in the unsupported lower
bound assumptions such as `CHAOS notin AL` and `ORDER notin NC`.
