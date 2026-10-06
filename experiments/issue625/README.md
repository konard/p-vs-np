# Issue 625: certified CircuitSAT membership

Both provers now supply unconditional `circuitSATInNP : InNP CircuitSAT`.
The finite verifier has 83 states and 332 instructions over the existing
four-symbol alphabet. Its universal correctness proof counts actual shared-model
`Run` instructions; the machine and circuit semantics are unchanged. The verifier
checks a supplied assignment, one fixed table handles every circuit, and the
runtime bound uses encoded input length (common-error families 15, 16, and 17).

## Proof structure

The paired `Idea41Core` modules retain the circuit encoding, exact decoder,
certificate bounds, `verifyCircuit`, and the Williams definitions and lemmas.
They let the syntax recognizer and evaluator share those definitions without
an import cycle. `Idea41` imports the core and the certified evaluator and
assembles the NP record. Existing theorem names remain available.

The paired [`CircuitVerifier.lean`](../../proofs/experiments/issue532/lean/CircuitVerifier.lean)
and [`CircuitVerifier.v`](../../proofs/experiments/issue532/rocq/CircuitVerifier.v)
contain the same finite table and prove its phases for arbitrary inputs:

- `malformed_reject` rejects every malformed encoding in exactly `|x| + 1` steps.
- `valid_start` preserves valid circuit and certificate cells and enters the
  length check in exactly `2 * |x| + 2` nonhalting steps.
- `count_success` restores every certificate bit when its length matches the
  unary header; `count_reject` rejects every other length. Both are polynomially bounded.
- `lookup_success` and `lookup_reject` handle arbitrary unary indices. The
  cursor advances once per unary tick, restores the circuit and wire cells,
  and rejects unavailable or forward wires.
- `gate_step` appends the NAND of the two selected operands; `gate_reject`
  rejects invalid operands. `gate_loop` proves the result equals
  `wfFromb |cert| C && output cert C` and bounds all gate instructions.
- `verifier_run` proves, for every word and every certificate, an actual run
  returning `verifyCircuit x cert` in at most
  `1024 * (|x| + |cert| + 12)^3` steps.
- `verifier_correct` fixes the answer and bound of every halting run by
  determinism; `verifier_accepts` equates machine acceptance with the check.

`circuitSATInNP_of_verifier_run` assembles membership with certificate polynomial
`⟨1, 1⟩` and time polynomial `⟨221184, 3⟩`. For
`N = |x| + |cert| + 1`, the latter evaluates to `221184 * (N + 1)^3`.
This is **known theorem mechanized: CircuitSAT belongs to NP**.
The six bridges named in the issue no longer take `CircuitSATInNP` as an
argument. The additional SAT-to-fast-CircuitSAT bridge also uses the proved
membership. `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup`, and other
unrelated Williams hypotheses remain explicit; this does not prove P ≠ NP.

## Completion and assumption gates

```sh
lake build
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
python3 experiments/issue625/check_membership.py --lean --rocq
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
bash experiments/issue625/check_repository.sh
```

The mandatory `CircuitSAT Completion (Lean)` and `CircuitSAT Completion (Rocq)`
CI jobs run on every configured event, including documentation-only PRs.
They require the unconditional theorem, all six exact bridge signatures,
exactly one manifest entry per target, admission-free local import closures,
and permitted transitive assumptions. The fixed ceiling is `propext`,
`Classical.choice`, and `Quot.sound` in Lean; Rocq must report a closed global
context. Changing an allowlist cannot bypass that ceiling.

Both jobs must pass for `Verification Summary` to pass. Failure, cancellation,
and skipping fail the summary. No completion check was relaxed to obtain this
proof. `test_completion_gate.py` tests the enforcement, including mutated
manifests, transitive admissions, and open assumption reports.

The explicit certified Rocq build compiles the core, syntax recognizer,
verifier, and membership module in dependency order. A workflow regression
checks that each local dependency precedes the module that imports it.

## Executable and kernel regressions

```sh
python3 -m unittest experiments.issue625.test_evaluator_candidate -v
python3 experiments/issue625/check_evaluator_candidate.py --lean --rocq
python3 experiments/issue625/check_verifier_reuse.py --lean --rocq
python3 experiments/issue567/check_machines.py --lean --rocq
python3 experiments/issue625/evaluator_candidate.py --word 101000 --certificate 0 --trace
```

The evaluator runner generates the table from `evaluator_candidate.py` and
kernel-checks its equality with the certified table. It checks fourteen
concrete runs and audits 29 interpreter, phase, and whole-verifier results.
The Python suite compares 3,174 bounded inputs against an independent
specification and checks 270 certificate-phase traces. Those experiments use
a finite quadratic budget; the universal theorem supplies the cubic bound.
Tracing is off by default. Generated sources and diagnostics are preserved
in the ignored `experiments/issue625/logs/` directory.

Four negative prover probes reject an impossible zero-step run, ignoring the
certificate, bypassing the length check, and allowing a forward wire. The
last two mutate actual transition rows; their finite witness runs disagree
with `verifyCircuit`. Unit tests also reject an admission in the whole run
proof and mixed open/closed Rocq assumption reports.

The reuse probes retain the counterexamples showing why the syntax table and
the SAT verifier cannot directly serve as this circuit verifier. Both use
`encCircuit 1 []`: syntax ignores certificate values, while the SAT table
reads a different encoding. These results do not rule out a machine reduction.

## Failure reproduced before the proof

The latest failing baseline was
[run 37477125164](https://github.com/konard/p-vs-np/actions/runs/37477125164)
on commit `d3674b34ae5fb980db7aa052ef9d4cab126bdadc`.
The run followed that commit; all six historical jobs passed while both
completion jobs and the summary failed. Logs were preserved under `ci-logs/`:
Lean line 857 reports missing `Issue532.Idea41.circuitSATInNP`, Rocq line 1522
reports missing `Idea41.circuitSATInNP`, and the following diagnostics identify
the six retained membership premises and missing certification entries.
Summary line 9594 reports the completion failures.

Before implementation, `check_membership.py --lean --rocq` reproduced those
same failures locally. The universal evaluator proof, NP assembly, bridge
updates, and manifest registrations address those failures directly. Current
validation and CI results are recorded in [PR 631](https://github.com/konard/p-vs-np/pull/631).
