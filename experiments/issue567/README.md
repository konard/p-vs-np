# Issue 567 regression experiments

`DecoderRegression.lean` and `DecoderRegression.v` contain the smallest
concrete encoding and verifier cases for the circuit-verifier slice. The Lean
file initially failed to elaborate because `decCircuit` was absent. The
paired `Assumptions` files print the axioms of the public decoder, verifier,
and residual-key theorems. Run the commands in
[`proofs/experiments/issue567/README.md`](../../proofs/experiments/issue567/README.md).

`MachineRegression.lean` and `.v` exercise the six-state circuit syntax machine
on actual charged runs, including malformed input. They also distinguish
syntax from wire well-formedness, reject short and long certificates in the
finite verifier, and prove that a pointwise-correct verifier cannot ignore its
certificate. The syntax machine intentionally checks only the encoding grammar.

After building the imported modules, run:

```sh
python3 experiments/issue567/check_machines.py --lean --rocq
```

The runner first compiles the unmodified regression files, then requires four
mutations to fail in each prover: a zero-step halt, replacing the certificate
by a fixed assignment, omitting its length check, and omitting the wire bounds.
It checks the failure diagnostic as well as the exit status so a broken import
does not count as a rejected mutation. Logs are kept in the ignored `logs/`
directory. These are mutation checks for the proven syntax slice and the finite
verifier; they do not claim a machine-level NAND evaluation proof.
