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

This exits 1 while the deliverable is incomplete. It compiles the exact
paired targets in `MembershipTarget.lean.in` and `MembershipTarget.v.in` against
`InNP CircuitSAT`, saving diagnostics in the ignored `logs/` directory. Lean
reports unknown identifier `Issue532.Idea41.circuitSATInNP`; Rocq reports that
`Idea41.circuitSATInNP` is not found. The paired `ConsequencesTarget` probes also
fail because all six bridges still require `CircuitSATInNP`.

## Mandatory CI completion gate

The 2026-10-06 review requires full completion through CI rather than accepting
the syntax slice. Previously the workflow omitted this failing diagnostic:
all seven jobs could pass while the exact membership target failed in both
provers. Compilation and auditing only the listed syntax results did not
check the issue's deliverable.

`CircuitSAT Completion (Lean)` and `CircuitSAT Completion (Rocq)` now run on
every configured event, including documentation-only PRs, independently of
the historical jobs' changed-file filters. Each builds the imported modules,
runs the existing machine mutations, then requires all of the following:

1. `circuitSATInNP` has the unconditional type `InNP CircuitSAT`, without a
   machine, a run theorem, or another membership proof as a parameter.
2. The six bridges named in issue 625 compile at their intended types without
   a `CircuitSATInNP` argument. The other Williams premises remain explicit.
3. All seven targets have exactly one entry at the expected source in
   `scripts/proof_status.json`.
4. The required sources and their local import closures contain no admissions
   or forbidden assumptions, even if entries are removed from the manifest.
   Each target's prover-reported assumptions also satisfy its registered
   limits and a fixed ceiling: only `propext`, `Classical.choice`, `Quot.sound`
   in Lean, and no global assumptions in Rocq. Expanding the manifest's
   allowlist cannot bypass that ceiling.

Both completion jobs must succeed for `Verification Summary` to succeed;
failure, cancellation, and skipping are all rejected. The completion jobs
upload their probe sources and logs on failure as well as success. They have
20-minute job limits. The repository's existing branch protection requires
`Verification Summary`; this change does not modify repository settings.

`python3 -m unittest experiments.issue625.test_completion_gate -v` reproduces
and tests the workflow and checker defect. Before the fix it fails on the
absent mandatory jobs and missing summary dependencies. After the fix it
checks failure propagation, registration, transitive admissions, expanded
allowlists, and global assumptions. These orchestration regressions pass;
the actual theorem gate fails until the proof is supplied. No expected-failure
wrapper converts missing membership into a successful CI result.

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

## CI failure investigation, 2026-10-06

The failing [run 37459212307](https://github.com/konard/p-vs-np/actions/runs/37459212307)
started at 11:51:35 UTC on `d1ea2a16cf6a3ba5488d072bdb7bfdc4d1c95941`,
after that commit at 11:51:17 UTC. Thus the failures are current. The branch
already contains the fetched default branch. The full downloaded log is
preserved locally as `ci-logs/formal-verification-37459212307.log`.

- Lean log line 1437 reports unknown identifier
  `Issue532.Idea41.circuitSATInNP`; lines 1439–1474 show that all six consequence
  contracts retain their membership premise.
- Rocq log line 1224 reports that `Idea41.circuitSATInNP` was not found;
  lines 1226–1235 show the first bridge's extra membership argument.
- Both jobs also reject missing certification entries. `Verification Summary`
  fails at line 9547 because the Lean completion job failed. Both completion
  jobs failed; the summary's first failing check exits before its Rocq check.

Full local Lean and Rocq builds reproduce successful compilation. The exact
completion command still exits 1, matching those missing proof obligations.
Recompilation, adding manifest entries alone, and changing job selection would
not supply the evaluator run theorem.

The paired `VerifierReuse` probes test two concrete implementation candidates:

```sh
python3 experiments/issue625/check_verifier_reuse.py --lean --rocq
```

Each prover proves that neither the syntax machine nor the existing SAT verifier
can satisfy even the weaker contract
`∀ x cert, |cert| ≤ |x| + 1 → ∃ t, Run m (pairedInput x cert) t (verifyCircuit x cert)`.
This contract omits the polynomial bound, so its refutation also rules out
using either table directly in `circuitSATInNP_of_verifier_run`.

Both counterexamples use `encCircuit 1 [] = [true, false, false]`. On certificate
`[false]`, the syntax table accepts while the circuit verifier rejects. On
`[true]`, the SAT table rejects while the circuit verifier accepts: SAT decodes
the first two bits as an empty clause and drops the trailing bit. These are
actual charged runs from the existing universal run lemmas, with disagreement
proved by run determinism. Their Lean assumption reports contain only
`propext` and `Quot.sound`; Rocq reports both results closed under the global
context. They establish counterexamples to direct table reuse, not the absence
of a possible circuit verifier or a circuit-to-SAT machine reduction.

The completion jobs run these probes before the existing mandatory membership
check and preserve their logs in the diagnostic artifacts. Issue 625 remains
unresolved and the PR remains draft: no full evaluator, polynomial run proof,
unconditional membership theorem, or premise removal is supplied here.

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
the current CI workflow and ends with the mandatory paired completion gate.
It now exits 1 at that gate on the incomplete tree. The Agda job uses the
workflow's pinned container. A passing build or syntax mutation suite alone
does not establish or certify unconditional circuit membership.
