# Issue 625 investigation and remaining evaluator obligation

Issue 625 asks for unconditional `circuitSATInNP : CircuitSATInNP` in Lean and
Rocq. **That target remains unresolved by this change.** The work here proves
and audits the machine-level encoding grammar slice and packages the NP-record
assembly, but supplies no full NAND-evaluating machine. No membership premise
is removed, and issue 625 should remain open.

## Reproduce the outstanding target

After building `Idea41` in both provers:

```sh
python3 experiments/issue625/check_membership.py
```

This intentionally exits 1 while the theorem is absent. It compiles the exact
paired targets in `MembershipTarget.lean.in` and `MembershipTarget.v.in`, saving
diagnostics in the ignored `logs/` directory. Lean reports unknown identifier
`Issue532.Idea41.circuitSATInNP`; Rocq reports that `circuitSATInNP` is not found.
This diagnostic is separate from the passing regressions for the completed
syntax slice. A passing CI suite for that slice does not close this target.

## Evidence and completed proofs

The starting repository has executable `verifyCircuit`, exact decoding,
certificate bounds, and `circuitSAT_iff_verifyCircuit`. It has no machine
implementing the evaluator and no polynomial bound on its runs. `SATVerifier`
provides an honest model for the eventual implementation: finite instruction
rows, tape invariants, and charged partial and halting runs.

The new paired `CircuitSyntax` modules use six explicit phases to parse the
regular grammar:

```text
header     = 1* 0
gate       = 1 (1* 0) (1* 0)
gate list  = gate* 0
```

`circuitSyntax_iff_decCircuit` proves exactness against the shared decoder.
`circuitSyntaxMachine_run` constructs an actual `Run` with exactly `|x| + 1`
instructions. `circuitSyntaxMachine_correct` fixes the time and answer of every
other run by determinism. Termination and acceptance are in
`scripts/proof_status.json`, and the paired assumption files print their
dependencies. This is **known theorem mechanized: linear-time recognition of
the circuit encoding grammar**.

`circuitSATInNP_of_verifier_run` proves that the full machine's bounded run
theorem would assemble `ClassNP` and membership. Its explicit parameter is:

```text
∀ x cert, |cert| ≤ |x| + 1 →
  ∃ t, t ≤ time.eval (|x| + |cert| + 1) ∧
    Run m (pairedInput x cert) t (verifyCircuit x cert)
```

This requires termination with the correct Boolean answer on every bounded
certificate, including malformed words and rejecting certificates. It is
stronger than merely showing that accepted certificates work. The theorem is
conditional, and an assumption audit does not discharge its explicit parameter.

## Designs examined and why they do not discharge membership

- Reusing the syntax table as the verifier is incorrect: it accepts
  `encCircuit 1 [(0, 1)]`, which has a forward wire. The full verifier rejects
  it. It also ignores certificate length and value.
- Reusing SAT's existing transition table requires a machine transformation
  from this circuit encoding to its distinct CNF encoding. No such machine
  reduction is supplied. NP closure under reductions is also an explicit
  unproved premise in Idea 23, so a function-level Tseitin construction alone
  would move the gap.
- The direct evaluator must retain certificate bits and computed wire values
  while performing unary-index lookups. Erasing certificate bits during a
  length-comparison pass would lose the values needed for gate evaluation.
  The syntax machine preserves the tape, but it does not construct the lookup
  workspace or prove an invariant for it.

No correct transition table and invariant for the full evaluator were obtained
in this investigation. Consequently there is no machine-level proof of forward
wire rejection, wrong-length rejection, or NAND evaluation and no overall
polynomial `Run` theorem. These remain the required next implementation work.

## Mutation checks and interpretation

```sh
python3 experiments/issue567/check_machines.py --lean --rocq
```

The runner compiles the baseline before requiring four mutants to fail in
each prover: zero-step halting, a fixed certificate, omitted length checking,
and omitted wire checking. These checks exercise real syntax runs and the
existing finite verifier. They do not claim the missing full machine is tested.
Both shorter and longer certificates are tested in the baseline.

The pointwise certificate relation must be preserved. The existential relation
`CircuitSAT x = true ↔ ∃ cert, verifyCircuit x cert = true` alone does not
exclude a certificate-blind exhaustive search algorithm. The tests therefore
also prove that any verifier equal to `verifyCircuit` on every certificate
cannot ignore it (a one-input empty circuit distinguishes `[true]` and `[false]`).

At a fixed arbitrary `t`, the literal equivalence
`Run m (pairedInput x cert) t true ↔ verifyCircuit x cert = true` cannot hold:
the right side can be true while `t = 0`, and `run_pos` rules out that run.
The proper obligations are bounded existence of a run and correctness of every
run; the assembly theorem uses these via run determinism.

Error-family checks: family 15 requires verifying the supplied assignment
rather than substituting search; family 16 requires one finite table for all
inputs; family 17 requires the bound to count instructions as a function of
encoded tape length. The syntax slice satisfies the latter two within its
limited scope. The full membership theorem still requires all three.

## Local validation

```sh
lake build
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
bash experiments/issue625/check_repository.sh
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

`check_repository.sh` retains the Python and prover regression commands from
the current CI workflow. The Agda job uses the workflow's pinned container.
The unconditional membership diagnostic above remains a separate failing check.
