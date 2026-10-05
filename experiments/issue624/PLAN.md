# Issue #624 work plan

Target: mechanize Cook–Levin hardness in the shared single-tape model, then
remove the hardness premises from the P = NP bridges. A completed endpoint
must provide `satHard`, `cookLevin`, paired assumption audits, and a checked
polynomial-time function machine. A smaller PR must not close #624.

- [x] Read #624 and all issue comments, PR #630 conversation/review comments,
  contributor guidance, and recent related PRs (#622 and #623).
- [x] Verify the prepared branch and clean initial working tree.
- [x] Inspect `ClassNP`, both `VerifierProgram` constructors, `Computes`,
  `encodeCNF`, and #568's existing `LocalTrace` semantics.
- [x] Write paired regressions before implementing the new modules; preserve
  their initial failures in `ci-logs/`.
- [x] Encode bounded, variable-length certificates as CNF using presence and
  value bits, a forced blank sentinel, suffix closure, and canonical blanks.
- [x] Prove model extraction, representation of every bounded certificate,
  and encoded bit length, counting the unary variable identifiers.
- [x] Connect the decoded certificate to #568's `LocalTrace` for both
  verifier constructors, preserving the actual certificate-dependent clock.
- [x] Prove a uniform polynomial time/window envelope without replacing the
  actual per-certificate acceptance condition by that envelope.
- [ ] Construct the full machine-transition tableau CNF and prove its two
  directions, with negative tests for rejecting verifiers and bad edges.
- [ ] Prove the full tableau's encoded polynomial size.
- [ ] Construct and verify a polynomial-time single-tape reduction machine;
  finite syntax and a size bound alone cannot discharge this obligation.
- [ ] Assemble hardness and completeness and remove the bridge premises only
  after the preceding obligations are checked.
- [x] Register only completed results in `scripts/proof_status.json`; add
  regression compilation to CI and `_CoqProject`.
- [x] Run the complete local Lean/Rocq builds, assumption audits, and relevant
  repository regressions, saving large outputs in `ci-logs/`.
- [x] Review the complete diff and document exact completed/open scope in the
  README, research log, and PR description. No restricted-verifier theorem,
  exponential search, or unchecked model import may stand in for hardness.
- [x] Fetch/merge the default branch as needed, commit validated atomic steps,
  push only `issue-624-0b9b9b6c5d75`, and update existing PR #630.
- [x] Check CI run timestamps and head SHA, preserve/analyze any failed logs,
  fix actionable failures, then mark the reviewed PR ready and verify clean
  git status. Do not mark #624 fixed unless its full endpoint is present.

Experiments use finite inputs. Stress probes, if needed, must have finite
input and memory/stack limits. No background process may be left unfinished.

## Continuation after the full-deliverable review

The review at https://github.com/konard/p-vs-np/pull/630#issuecomment-5993763999
requires the complete #624 endpoint, including the reduction machine. The
edited PR description is not evidence that the missing proofs exist.

- [x] Read the complete issue, updated PR body, all three PR comment/review
  endpoints, contributor guidance, and the existing proof construction.
- [x] Check the prepared branch and recent CI timestamps/SHAs. Existing CI
  passes for `913f9fa`; the default branch has not advanced.
- [x] Trace the configuration boundaries and exact certificate-dependent
  clocks needed to compile `LocalTrace` constraints into finite CNF.
- [ ] Develop finite negative regressions before implementing each missing
  construction; retain diagnostics in `ci-logs/` and probes here.
- [x] Prove exact-clock recovery, two-way padding simulation, fixed-window
  trace/language correspondence, and the explicit polynomial width.
- [x] Prove local implication and exactly-one CNF contracts and unary
  encoded-size bounds; compile their paired negative regressions.
- [x] Prove a finite fixed-word emitter's charged `Computes` contract,
  reusable writing/return blocks, and paired concrete execution regressions.
- [ ] Construct and verify transition/acceptance CNF, both model directions,
  and all required rejecting/bad-edge/certificate-bound cases.
- [ ] Prove the complete encoded size, including unary variable identifiers.
- [ ] Implement the finite single-tape emitter and prove its `Computes`
  contract and polynomial step bound. Use existing sequencing/sweep proofs.
- [ ] Assemble paired `satHard`/`cookLevin`, audit their assumptions, remove
  every named hardness premise, and update the manifest and Idea dossiers.
- [x] Run complete local CI and both assumption audits, inspect the staged
  proof diff, and commit verified construction steps.
- [ ] Publish the complete deliverable and verify its full PR diff and CI;
  push only the prepared branch.
- [ ] Update PR #630 around the implemented result, check fresh CI against
  the pushed SHA, download/analyze any failing logs, and verify clean status.
- [ ] Mark the PR ready once the deliverable is proved and reviewable. Keep
  any unresolved proof obligation explicit; do not replace it by an axiom,
  admissions, exponential enumeration, or a weakened machine model.

## Validated checkpoint

The certificate CNF and semantic verifier interface are complete. All four
unchecked construction items above remain open, including the rest of slice 1.
The complete local Lean, Rocq, Agda, and Python workflow checks passed. Both
whole-manifest assumption audits passed; see [ASSUMPTIONS.md](ASSUMPTIONS.md).

[CI run 37290702071](https://github.com/konard/p-vs-np/actions/runs/37290702071)
passed all seven checks on `dcdf2267009c7ce3aee3261df2668d52e3df2cb4`.
Its creation time, 2026-10-05 09:32:24 UTC, is after that commit's
09:31:44 UTC timestamp. This checkpoint records the tested proof sources;
subsequent changes are checked by the PR's latest CI run.
Publication and readiness are tracked on [PR #630](https://github.com/konard/p-vs-np/pull/630),
whose description contains no issue-closing reference.

## Continuation checkpoint

The fixed-window semantic interface, local CNF combinators, and fixed-word
output primitive are checked in both provers. The full `tableauCNF`, its size
polynomial, the input-dependent reduction machine, and `satHard`/`cookLevin`
remain absent. [TABLEAU_DESIGN.md](TABLEAU_DESIGN.md) records the concrete
remaining construction and the emitter quantifier-order obligation. The
existing hardness premises must remain until those proofs are available.
