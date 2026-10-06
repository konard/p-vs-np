# Issue 567: circuit verifier slice and a residual-key counterexample

**Status:** a known circuit-verification fact mechanized in part, plus a scoped
adversarial result. Issue 625 completes `CircuitSATInNP` using this encoding layer. The work does
not establish `NP ⊈ P` or a time lower bound for a SAT solver.

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
check is implemented by the finite evaluator added for issue 625, with a
universal polynomial `Run` bound. `Idea41.circuitSATInNP` is unconditional,
and the Idea 41 and issue 10 bridges use that proof.

### Machine-level syntax slice (issue 625)

The paired `CircuitSyntax` modules provide a six-state `Complexity.Machine`
that recognizes exactly the `encCircuit` grammar on `pairedInput x cert`.
`circuitSyntax_iff_decCircuit` connects it to the existing total decoder.
`circuitSyntaxMachine_run` proves a run with exactly `|x| + 1` charged
instructions for **every** input and certificate, including malformed input.
`circuitSyntaxMachine_terminates` gives the explicit polynomial `⟨1, 1⟩`,
and `circuitSyntaxMachine_accepts_iff` identifies the accepted encodings.
The machine leaves all input and certificate symbols intact.

This is **known theorem mechanized: linear-time recognition of the circuit
encoding grammar**. It is not the full circuit verifier. For example,
`encCircuit 1 [(0, 1)]` has valid syntax but an invalid forward wire, and the
syntax machine accepts it. The machine does not check certificate length or
evaluate NAND gates. Its certified status applies only to the listed syntax
theorems.

`Idea41.circuitSATInNP_of_verifier_run` now proves the NP-record assembly from
a machine and a polynomial satisfying the **explicit** run contract:

```text
∀ x cert, |cert| ≤ |x| + 1 →
  ∃ t, t ≤ time.eval (|x| + |cert| + 1) ∧
    Run m (pairedInput x cert) t (verifyCircuit x cert)
```

It uses the existing certificate bound and run determinism. The paired
`CircuitVerifier.verifier_run` theorems now discharge that contract for an
83-state evaluator within `1024 * (|x| + |cert| + 12)^3` instructions.
The [issue 625 proof](../../../experiments/issue625/README.md) records
unconditional membership, removed premises, and assumption audits. The syntax
machine remains a separate recognizer with the narrower contract above.

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
reports a closed global context. The syntax and residual-key conclusions take
no problem-specific hypothesis; the assembly theorem retains its evaluator-run
hypothesis, discharged in `Idea41` by the full evaluator. Other major premises are
`PSubsetPPoly`, `SATHard` (for the converse clocked-SAT bridge), and the
Williams/hierarchy premises described in Idea 41. The Williams premises remain explicit.

```sh
lake build proofs.experiments.issue532.lean.Idea41
lake build proofs.experiments.issue567.lean.ResidualKey
lake build proofs.experiments.issue567.lean.CircuitSyntax \
  proofs.experiments.issue10.lean.NPNotSubsetP
lake env lean experiments/issue567/DecoderRegression.lean
lake env lean experiments/issue567/Assumptions.lean
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq experiments/issue567/DecoderRegression.vo \
  experiments/issue567/Assumptions.vo \
  experiments/issue567/MachineRegression.vo \
  proofs/experiments/issue567/rocq/ResidualKey.vo
python3 experiments/issue567/check_machines.py --lean --rocq
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The regression files cover exact decoding, trailing/truncated bits, a forward
wire, a gate with no input wire, accepted/rejected NAND certificates, wrong
certificate length, and the no-gate output convention. The adversarial
family theorem checks both SAT answers independently through `evalCNF`.
