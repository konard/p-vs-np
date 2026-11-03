# Issue 567 regression experiments

Status at 2026-11-03: regression checks for the circuit decoder and verifier
in `Issue532.Idea41` and for the `ResidualKey` counterexample. They do not
prove `CircuitSATInNP`, which is still a named premise on `main`.

`DecoderRegression.lean` and `DecoderRegression.v` contain the smallest
concrete encoding and verifier cases for the circuit-verifier slice. The Lean
file initially failed to elaborate because `decCircuit` was absent. The
paired `Assumptions` files print the axioms of the public decoder, verifier,
and residual-key theorems. CI compiles `DecoderRegression.lean` in the Lean job. `DecoderRegression.v` and
`Assumptions.v` are in `_CoqProject`, so the Rocq job compiles them. CI does
not run `Assumptions.lean`. Run the commands in
[`proofs/experiments/issue567/README.md`](../../proofs/experiments/issue567/README.md).
