# Issue 567: circuit verifier slice and a residual-key counterexample

**Status:** a known circuit-verification fact mechanized in part, plus a scoped
adversarial result. This work does not establish `CircuitSATInNP`, `NP ⊈ P`, or
a time lower bound for a SAT solver.

## Circuit verifier slice

The Lean `Idea41` file now has an executable decoder for the exact shared
`encCircuit` format. It parses unary input and gate indices, bounds list
recursion by word length, and checks the reconstructed encoding to reject
trailing or malformed bits. `decCircuit_encCircuit` and `decCircuit_sound` prove
round-trip and exactness. The existing Rocq decoder has the same properties.

In both provers, `wfFromb` checks that each gate reads only earlier wires;
`checkCircuit_iff` identifies precisely the well-formed encodings.
`verifyCircuit` checks certificate length and evaluates the existing NAND
`output`. `circuitSAT_iff_verifyCircuit` proves that its accepted certificates
are exactly witnesses for the shared `CircuitSAT` language, including the
zero-input convention. `decCircuit_data_bounds`, `verifyCircuit_cert_bound`,
and `wires_length` bound the parsed input count, gate count, certificate
length, and intermediate wire-list length by the encoded data size.

The Lean `CircuitSAT` remains a classical truth predicate, but its acceptance
relation is now proved equivalent to an executable certificate check. The
check is implemented in the prover, not yet by a finite `Complexity.Machine`
on `pairedInput`; no polynomial `Run` bound has been proved. Consequently the
named `CircuitSATInNP` premise in Idea 41 and issue 10 remains explicit.

## Adversarial claim for issue 568

The paired `ResidualKey` files challenge one precisely specified **proposed**
memoization key: `(numVars φ, number of clauses, |encodeCNF φ|)`. For every
`k ≥ 0`, `satFamily k` has two positive unit clauses followed by `k` more;
`unsatFamily k` replaces the first with a negative unit clause. Both use one
variable, have `k + 2` clauses, and encode to `4(k + 2)` bits. Their keys are
equal, but the first is satisfiable and the second is unsatisfiable. The
theorem `coarseKey_not_satisfiability_complete` proves this for all `k`; it
refutes answer reuse **solely** by that key. It does not challenge a full
canonical residual formula key or a current version of the issue 568 DPLL
solver. In particular, equal counts alone imply no runtime lower bound.

## Verification and dependencies

The public conclusions are listed in `scripts/proof_status.json`. Lean reports
only `propext`, `Classical.choice`, and `Quot.sound` where applicable; Rocq
reports a closed global context. No new theorem takes a problem-specific
hypothesis. The remaining major premises are `CircuitSATInNP`,
`PSubsetPPoly`, `SATHard` (for the converse clocked-SAT bridge), and the
Williams/hierarchy premises described in Idea 41. No premise is discharged
by this slice.

```sh
lake build proofs.experiments.issue532.lean.Idea41
lake build proofs.experiments.issue567.lean.ResidualKey
lake env lean experiments/issue567/DecoderRegression.lean
lake env lean experiments/issue567/Assumptions.lean
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq experiments/issue567/DecoderRegression.vo \
  experiments/issue567/Assumptions.vo \
  proofs/experiments/issue567/rocq/ResidualKey.vo
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The regression files cover exact decoding, trailing/truncated bits, a forward
wire, a gate with no input wire, accepted/rejected NAND certificates, wrong
certificate length, and the no-gate output convention. The adversarial
family theorem checks both SAT answers independently through `evalCNF`.
