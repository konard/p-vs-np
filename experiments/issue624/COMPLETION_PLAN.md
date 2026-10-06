# Enforced completion of issue #624

Review: https://github.com/konard/p-vs-np/pull/630#issuecomment-6014215588

The completion check must fail until the entire deliverable is checked. Green
prerequisite audits, a draft/ready flag, or an edited PR description cannot
establish completion. No formal impossibility has been established.

- [x] Read the full issue, updated description, conversation comments, inline
  comments, reviews, contributor guidance, and existing construction plans.
- [x] Verify the prepared branch, clean initial tree, latest CI SHA/timestamp,
  and inclusion of the current default branch.
- [x] Reproduce the gap with regressions: prerequisite certification alone
  must not satisfy the completion check.
- [x] Add paired acceptance type checks for the complete tableau, both
  model directions, unary encoded size, one input-independent reduction
  table, `satHard`, `cookLevin`, negative cases, and unconditional bridges.
- [x] Reuse the certified source/import and assumption checker. Reject missing
  manifest entries, admissions, disallowed assumptions, and extra premises.
- [x] Add an independent completion job on every update of PR #630, including
  documentation-only changes. Make Verification Summary fail on a missing,
  skipped, cancelled, or failing completion job for this PR.
- [x] Require GitHub Actions' Verification Summary check on `main`, with
  strict up-to-date checks and administrator enforcement. Confirm the previous
  branch had no protection or rulesets before adding this requirement.
- [x] Verify checker regressions, existing workflow regressions, full local
  compilation and audits. Store large logs in `ci-logs/` and inspect them.
- [x] Finish the full tableau construction and explicit encoded-size polynomial
  in both provers.
- [ ] Finish the finite reduction machine and charged `Computes` proof.
- [ ] Assemble hardness/completeness, remove the specified bridge premises,
  update dossiers and documentation, and pass the completion check.
- [x] Commit reviewed enforcement changes and push only the prepared branch.
- [ ] Update PR #630; check new CI run SHA/timestamp, download non-passing
  logs, and report their precise errors. Leave the PR draft while completion
  fails; mark it ready only after the full deliverable passes.

Experiments use finite inputs; deliberate stress probes require memory/stack
limits. Wait for every background command before ending work. Preserve the
shared machine semantics and reuse #568's `LocalTrace`.

## Accepting-trace continuation

- [x] List the latest five CI runs with timestamps and SHAs. Confirm run
  `37466019639` checks `43a39de` after that commit was created. Download all
  three recent failing runs to ignored `ci-logs/` and read the failed job.
- [x] Reproduce the 58 missing-contract/registration diagnostics locally.
  The summary fails because the full Cook–Levin completion check fails;
  prerequisite compilation and assumption checks pass.
- [x] Fetch `origin/main` and verify it is already an ancestor of this branch.
- [x] Add paired finite accepting-prefix regressions before creating `RunCNF`;
  preserve missing-module failures and intermediate proof goals locally.
- [x] Assemble row constraints, charged successors, accepting halts, and
  finite clock exhaustion. Extract the original #568 trace from every model
  and construct/decode the canonical assignment for every valid trace.
- [x] Prove clause count, variable bounds, width, actual unary encoded size,
  and an explicit polynomial envelope. Reuse shared polynomial arithmetic.
- [x] Register all 24 paired `RunCNF` lemmas and the two paired shared
  polynomial lemmas with their exact kernel-reported assumptions.
- [x] Run the full Python, Lean, Rocq, and Agda checks; inspect saved logs and
  the PR diff. The 254-job Lean build and both 204-result kernel audits pass.
  Commit shared polynomial arithmetic separately from the trace compiler.
- [ ] Push only the prepared branch, update PR #630, verify the fresh run's
  SHA/timestamp, and download/analyze every non-passing job log.
- [x] Wire the initial input and decoded certificate into row zero; prove
  full `tableauCNF` correctness and combine all fragment size bounds.
- [ ] Construct the input-independent finite reduction table and prove its
  charged polynomial `Computes` contract, then assemble the public endpoints.

The trace compiler imposes no initial configuration. Its rejecting-machine
theorem assumes rejection from every configuration, rather than from just the
verifier's prescribed input. It does not discharge the verifier-level
completion contract. The full completion check remains required.

## Initial-input continuation of issue #624

- [x] Read the issue, all PR conversations/reviews/inline comments, contributor
  guidance, existing construction plans, and recent related merged PRs.
- [x] Verify the prepared branch and initial clean tree. Fetch the latest
  default branch; `origin/main` is already included, with no conflicts.
- [x] Download the five most recent failed runs to ignored `ci-logs/`, verify
  timestamps/SHAs, and reproduce the 58 completion diagnostics locally.
- [x] Add paired full-tableau regressions before implementing the missing
  initial row. Preserve their initial failures in `ci-logs/`.
- [x] Compile symbolic input/certificate cells without enumerating certificates.
  Prove the exact initial-row contract for both verifier constructors.
- [x] Assemble the complete tableau CNF, both model directions, input-language
  equivalence, rejecting/overlong/wrong-successor negative cases, and the
  explicit polynomial bound on actual unary-encoded output length.
- [ ] Build the single input-independent finite reduction machine and its
  charged polynomial `Computes` proof; assemble paired hardness/completeness
  and remove every specified hardness premise.
- [x] Register checked conclusions, attach kernel assumptions, update docs,
  and run all local Python/Lean/Rocq/Agda checks with logs saved to files.
- [ ] Review code, tests, and PR diff; commit useful atomic steps, push only
  `issue-624-0b9b9b6c5d75`, update PR #630, and inspect fresh CI logs.
- [ ] Verify the full completion checks pass and the tree is clean; mark the
  PR ready only once its required full deliverable is checked.

The failing summary is downstream of the intentionally mandatory completion
gate. Keep its contracts and assumption policy intact. No formal impossibility
has been established. Experiments use finite inputs; any deliberate stack or
memory stress must be resource-bounded. Wait for background checks to finish.

### Current checked construction

The paired `InitialCNF` and `CookLevin` modules prove the complete tableau
model correspondence and its actual unary encoded-size polynomial. Thirty new
public conclusions per prover are registered using kernel-reported assumptions.
The seven tableau endpoints match the completion gate’s original types. Concrete
regressions reject wrong initial state/head/tape contents and cover empty, short,
full, and zero-bound certificates with both verifier constructors.

The local completion preflight now has 42 diagnostics, down from 58. The
remaining endpoints are `red_computes`, `satHard`, and `cookLevin` in each
prover, plus the existing public bridge premises/registrations. Polynomial
output size is proved; polynomial charged running time is not. No single
input-independent finite reduction table, its tape invariants, or its `Computes`
proof has been constructed.
The mandatory completion gate remains unchanged.

Local validation at the initial-input checkpoint passed: the complete Python
suite, 256-job Lean build, full Rocq build, both 234-result source/assumption
audits, seven original tableau contract types in each kernel, and Agda checks.
Workflow lint and `git diff --check` also passed. Expected negative kernel
probes were rejected.

The existing Idea 36 bridge also matches the completion gate's required type.
Its missing registration is fixed in both provers; `existing_bridge_probe.py`
checks the exact type and assumptions. Its separate vertex-cover hardness
premise remains required. That checkpoint registered 235 conclusions per prover.

## Input-retaining counter continuation

- [x] Read the issue and all PR comment types; fetch the latest default branch.
  `main` remains `ecedd2b` and is already an ancestor of this branch.
- [x] List the latest five failed runs, download their full logs into ignored
  `ci-logs/`, and verify run `37481919026` follows and checks `7ae9e283`.
  The local preflight reproduces its 42 diagnostics. Full log lines 917–959
  identify the endpoints/premises; line 9567 reports the downstream summary.
- [x] Add paired counter regressions before implementation; preserve the
  initial missing-module failures in `ci-logs/counter-before-{lean,rocq}.log`.
- [x] Prove shared symbol-preserving left/right scans, `Reaches` composition,
  and shifted second-table embedding; reuse composition in the fixed emitter.
- [x] Construct a fixed nine-state input-retaining counter with an exact
  charged tape contract for every word, prefix, and existing unary counter.
- [x] Construct a seven-state setup block, retaining the actual input and
  inserting cursor/delimiter. Sequence a 16-state `countedInput` machine with
  an exact `Reaches` contract from `initial x` and bound `12 * (|x| + 1)^2`.
- [x] Register 11 conclusions per prover using actual kernel assumptions;
  integrate paired regressions and certified builds into local checks and CI.
- [ ] Finish arithmetic/copy/formula-emission blocks and tape restoration;
  prove `red_computes`, assemble hardness/completeness, and remove premises.
- [x] Finish full Python/Lean/Rocq/Agda verification and review the diff.
  The 257-job Lean build, full Rocq build, both 246-result source/assumption
  audits, tableau/bridge contract checks, workflow lint, and focused project/
  workflow tests pass. Logs are preserved in `ci-logs/counter-full-*.log`.
  The completion preflight still exits 1 with the same 42 diagnostics.
- [x] Commit atomic changes, push only the prepared branch, and update PR #630.
- [x] Investigate fresh run `37489428127`, created at `15:40:02Z` after
  `ec9e8aa` at `15:39:48Z`. The certified Lean job missed the new module in
  its explicit build list; saved log line 428 reports missing
  `UnaryCounter.olean`. All other prerequisite jobs passed. Add a paired
  certification-build coverage regression that fails on this omission,
  then include `UnaryCounter` in the Lean certification targets. The
  regression, target build, and workflow lint pass after the fix.
- [ ] Inspect fresh CI logs against the pushed SHA and timestamp; record their
  findings in the PR description.
- [ ] Verify the full deliverable and all CI pass, then mark PR #630 ready.

The counter's output is a tape-block configuration, not `Computes red`.
No formula-emitting reduction table or charged bound for it is established.
All probes use finite inputs; no deliberate stack or memory stress is used.
