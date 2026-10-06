# Issue 624 continuation after instruction dispatch

Goal: satisfy the complete paired Cook–Levin contracts required by issue #624
and PR #630. Preserve the shared machine semantics, assumption policies,
completion gate, and branch protection. Partial construction does not meet
the endpoint.

## Investigation

- [x] Verify the prepared branch and initially clean working tree.
- [x] Read the issue and all issue/PR conversation comments, inline comments,
  reviews, contributor guidance, existing construction notes, and recent
  related merged PR titles.
- [x] Fetch the default branch and verify it is included without rewriting
  history. `origin/main` is `ecedd2b`; `HEAD...origin/main` reports `11 0`.
- [x] List five recent CI runs with timestamps and head SHAs; verify the
  newest run follows the latest commit and checks its exact SHA.
- [x] Preserve both failing runs in `ci-logs/verification-37459726940.log`
  and `ci-logs/verification-37455021867.log`; inspect the completion and
  summary diagnostics in chunks smaller than 1,500 lines.
- [x] Reproduce the 58 completion diagnostics locally in
  `ci-logs/issue624-completion-start.log`.
- [x] Trace the current finite-window/tableau definitions and their exact
  relationship to `step`, including both directions and boundary behavior.

## Construction

- [x] Add minimum paired regression cases before the next implementation;
  keep experiments finite and preserve failure logs.
- [x] Compile successor head/state/tape constraints using shared CNF helpers
  and prove decoding agrees with the existing charged machine step.
- [ ] Connect initial/certificate constraints, active rows, and accepting
  termination into the complete `tableauCNF` for every `ClassNP` witness.
- [ ] Prove complete extraction, representation, language equivalence, and
  the three requested full-formula negative cases.
- [ ] Prove polynomial encoded bit length using the original unary encoding.
- [ ] Construct one finite input-independent reduction table and prove its
  charged polynomial `Computes` contract, including final tape and head.
- [ ] Assemble `satHard` and `cookLevin` in Lean and Rocq; remove all specified
  bridge premises and update manifest entries, dossiers, and research notes.

## Verification and publication

- [x] Run focused regressions, full local verification, assumption audits,
  and completion checks; save large logs to `ci-logs/` and inspect them.
- [x] Review the complete PR diff for regressions and requirement coverage.
- [ ] Commit each validated atomic step, and push only
  `issue-624-0b9b9b6c5d75` without rewriting history.
- [ ] Update PR #630 title/body with concrete changes, reproductions,
  assumption reports, and validation evidence.
- [ ] Check fresh CI SHA/timestamps; download and investigate every failure.
- [ ] Mark PR #630 ready only when the full deliverable and CI pass; verify
  the working tree is clean and wait for all background work before finishing.

## Local verification checkpoint

The focused paired regressions and all four local verification suites
(`check.sh python`, `lean`, `rocq`, and pinned-container `agda`) pass.
Both 178-result assumption audits pass; the 38 new conclusions per prover
are recorded in `ASSUMPTIONS.md`. Every new Lean policy is restricted to
its actual report, and every new Rocq policy permits no assumptions.
The finite diagnostic probes also pass. Full-build logs remain local under
`ci-logs/issue624-full-*.log`.

The complete-deliverable preflight was rerun after the construction and
still fails with 58 missing-result/premise diagnostics in
`ci-logs/issue624-completion-current.log`. No theorem implementing the
full tableau or input-dependent reduction was produced. The uncompleted
construction items above are still the blockers; this checkpoint is not
completion of #624. Publication and fresh workflow results are recorded
in PR #630.
