# Issue 567 regression experiments

`DecoderRegression.lean` and `DecoderRegression.v` contain the smallest
concrete encoding and verifier cases for the circuit-verifier slice. The Lean
file initially failed to elaborate because `decCircuit` was absent. The
paired `Assumptions` files print the axioms of the public decoder, verifier,
and residual-key theorems. Run the commands in
[`proofs/experiments/issue567/README.md`](../../proofs/experiments/issue567/README.md).
