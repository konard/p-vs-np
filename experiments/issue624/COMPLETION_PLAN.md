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
