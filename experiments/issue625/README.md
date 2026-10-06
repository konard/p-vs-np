# Issue 625 investigation and remaining evaluator obligation

Issue 625 asks for unconditional `circuitSATInNP : CircuitSATInNP` in Lean and
Rocq. **That target remains unresolved by this change.** The work here proves
and audits the machine-level encoding grammar slice, packages the NP-record
assembly, and implements a direct evaluator candidate. Its universal evaluator
correctness and polynomial `Run` proof remain missing. No membership premise
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

The initial investigation did not obtain an evaluator table. The bounded
candidate experiment below now supplies a prospective table, but its whole
evaluator correctness and polynomial `Run` theorem remain unproved. Concrete
runs do not discharge these obligations.

## Direct evaluator candidate, 2026-10-06

[`evaluator_candidate.py`](evaluator_candidate.py) constructs an 83-state,
332-instruction table over the unchanged four-symbol alphabet. Its execution
function follows `Complexity.moveHead`, including explicit blank cells. The
instruction table does not call the reference decoder or circuit evaluator.

The table first validates the circuit grammar. It compares the unary input
count with certificate length while retaining all certificate values: a single
cursor marks a false wire with `blank`, a true wire with `separator`, and each
cursor cell is restored before that pass completes. During a gate lookup the
active gate's list marker becomes `blank`. The machine consumes unary ticks
by marking them with `separator` and shuttles to the wire cursor once per
tick. Reaching the end of the wire list rejects an unavailable or forward
wire. Both indices are restored after lookup. The finite state retains the
first operand while looking up the second, then appends their NAND to the
wire region and restores the gate marker. The final pass returns the last
wire, with `false` for an empty wire list.

The intended invariants still need general proofs:

1. Each phase finds the intended boundary or marked cell, including when the
   marked false wire is adjacent to the blank beyond the wire list.
2. A lookup's consumed unary prefix and wire cursor advance together; lookup
   succeeds exactly when its index is below the current wire-list length.
3. Restoring a lookup preserves the original circuit cells and every wire
   value. Appending a gate produces the same list as `Circuits.wires`.
4. Certificate matching and all lookup-failure exits terminate. The number
   of shuttles and their charged instructions have one explicit polynomial
   bound in the encoded paired-input length.

### Universally proved candidate phases

The paired [`EvaluatorInvariants.lean.in`](EvaluatorInvariants.lean.in) and
[`EvaluatorInvariants.v.in`](EvaluatorInvariants.v.in) are compiled with the
exact candidate table. State references are filled from that table's state
index, so these are proofs about its charged instructions. They establish:

- `malformed_reject`: every word outside the circuit encoding grammar is
  rejected for every certificate in exactly `|x| + 1` instructions.
- `valid_start`: every syntactically valid word reaches `count_first` in
  exactly `2 * |x| + 2` nonhalting instructions. The circuit and certificate
  cells are preserved, with an explicit blank at the left end of the tape.
- `lookup_first_initial`: for every bit-word suffix and nonempty wire list,
  the first lookup marks the first wire and returns to the active gate in
  exactly `2 * |suffix| + 4` nonhalting instructions, preserving all other
  cells. This covers both false/blank and true/separator cursor encodings.
- `gate_empty_run`: when the gate loop reaches its final list marker, it
  returns the last wire, defaulting to false on an empty wire list, in exactly
  `|wires| + 3` instructions.

These results quantify over arbitrary words and tape contexts. They are not
finite-input examples. They still do not prove the certificate-matching
phase, advancement of the wire cursor for arbitrary unary indices, operand
and marker restoration, or NAND appending. Consequently no whole verifier
run bound, `circuitSATInNP`, or premise-free bridge follows from them.

The runner scans the generated source and its local imports for admissions
and forbidden assumptions, then checks every printed assumption report. The
new phase results use only `propext` and `Quot.sound` in Lean; Rocq reports
closed global contexts. Regression tests reject a later Lean admission, a
mixture of closed and open Rocq reports, and missing reports. These candidate
phase proofs have not been registered as unconditional membership results.

The bounded Python suite compares the table against an independent executable
specification on 3,174 input/certificate pairs. It covers all raw words up to
eight bits with four representative certificates, identity and NAND circuits,
two-gate dependencies, wrong certificate lengths, forward wires, and wire
lookups with up to sixteen input wires. Each run has a finite budget of
`128 * (|x| + |cert| + 2)^2`. Exceeding the budget fails the experiment;
**that budget has not been proved sufficient on arbitrary inputs**.

[`check_evaluator_candidate.py`](check_evaluator_candidate.py) emits the same
table as `Complexity.Machine` in Lean and Rocq and kernel-checks fourteen
concrete runs against the actual `verifyCircuit` definitions. For example,
`encCircuit 1 [(0, 0)]` takes 111 charged steps on either one-bit certificate
and returns the appropriate NAND result. A two-gate dependency takes 515
steps on `[true, false]`. The generated probes also prove `execute_sound` and
`execute_complete` for every machine: their bounded interpreter and `Run`
agree on the exact time and answer. The printed Lean dependencies are within
`propext` and `Quot.sound`; Rocq reports closed global contexts.

```sh
python3 -m unittest experiments.issue625.test_evaluator_candidate -v
python3 experiments/issue625/check_evaluator_candidate.py --lean --rocq
python3 experiments/issue625/evaluator_candidate.py --word 101000 --certificate 0 --trace
```

Tracing defaults to off. Generated probe sources and prover logs are preserved
in `experiments/issue625/logs/`. The new checks run before the unchanged
mandatory membership gate. They are experimental evidence, **not certified
CircuitSAT membership**. Neither prover yet supplies `circuitSATInNP`, the
membership premises remain, and the PR remains draft and incomplete.

## CI failure investigation, 2026-10-06

The run at the beginning of this investigation,
[37465392079](https://github.com/konard/p-vs-np/actions/runs/37465392079),
started at 12:43:55 UTC on `39bd105e46cf663e07c68786c8506eaf0ab88425`,
after that commit at 12:43:49 UTC. Thus the reported failures are current.
The branch already contains the fetched default branch `ecedd2b`.
Full logs for all four failed runs among the latest five were downloaded into
the ignored `ci-logs/` directory. In `verification-37465392079.log`:

- Candidate concrete-run probes pass at Lean line 843 and Rocq line 1500.
- Lean line 850 reports unknown identifier
  `Issue532.Idea41.circuitSATInNP`; the six bridge errors begin at line 852
  because their types still have the membership premise.
- Rocq line 1509 reports that `Idea41.circuitSATInNP` was not found; the
  bridge type mismatch begins at line 1512 for the same reason.
- Both jobs reject missing certification entries. The summary fails at line
  9600 after the Lean completion failure. Both completion jobs and the summary
  fail; all six other jobs pass.

This run precedes the four universal phase proofs above. The updated probes
pass locally in both provers, while the exact membership targets retain the
same failure. Fresh CI results for the updated head are recorded in PR #631.

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
unresolved and the PR remains draft: the candidate has concrete checked runs,
but no universal evaluator proof, polynomial run proof, unconditional
membership theorem, or premise removal is supplied here.

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
On the updated tree, all 132 Python tests and the preceding prover regression
checks pass, including the four universal candidate phase results. The script
then exits 1 at the membership gate. Full Lean and Rocq builds, the certified
source and assumption audits in both provers, and the six Agda checks in the
workflow's pinned container pass. A passing build or phase invariant alone
does not establish or certify unconditional circuit membership.
