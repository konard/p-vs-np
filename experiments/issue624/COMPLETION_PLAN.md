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
- [ ] Finish the outstanding tableau construction, explicit size polynomial,
  finite reduction machine and charged `Computes` proof in both provers.
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
- [ ] Wire the initial input and decoded certificate into row zero; prove
  full `tableauCNF` correctness and combine all fragment size bounds.
- [ ] Construct the input-independent finite reduction table and prove its
  charged polynomial `Computes` contract, then assemble the public endpoints.

The trace compiler imposes no initial configuration. Its rejecting-machine
theorem assumes rejection from every configuration, rather than from just the
verifier's prescribed input. It does not discharge the verifier-level
completion contract. The full completion check remains required.
