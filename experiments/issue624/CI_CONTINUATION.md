# CI diagnosis and instruction dispatch construction

This continuation follows the requirement to keep PR #630 blocked until all
of issue #624 is proved. No formal impossibility of the deliverable has been
proved, and the instruction compiler below does not resolve it.

## Investigation

- [x] Read issue #624 and every issue/PR conversation comment, inline comment,
  and review. Read contributor guidance and the latest related merged PRs
  (#622 and #623).
- [x] Verify branch `issue-624-0b9b9b6c5d75` and a clean initial working tree.
- [x] Fetch `origin/main` and merge it without rewriting history. The latest
  default-branch commit remains `ecedd2b45f1c524d85c00b2da27a9c140025550c`;
  it was already included, so the merge reports “Already up to date.”
- [x] List the latest five CI runs with timestamps and head SHAs. The newest
  failed run is [37455021867](https://github.com/konard/p-vs-np/actions/runs/37455021867),
  created at `2026-10-06T11:13:56Z`, after its head commit `3d783e6` at
  `11:13:34Z`. The previous four runs passed without the completion gate.
- [x] Download the full failed log to
  `ci-logs/verification-37455021867.log` and inspect the completion and summary
  job diagnostics in chunks smaller than 1,500 lines.
- [x] Reproduce with `python3 scripts/check_issue624_completion.py`, preserving
  `ci-logs/issue624-completion-reproduced.log`.

The fresh failure is mathematical incompleteness, not a stale run or a failed
existing compiler. Log lines 244–253 name the absent Lean tableau contracts,
size theorem, reduction, hardness, completeness, and full-formula negative
tests; lines 273–282 name the paired Rocq gaps. Lines 254–257 and 283–286
show existing explicit hardness premises. Line 9264 reports
`Issue 624 completion did not pass (failure)` in the required summary.
All six other jobs in that run pass.

## Construction and validation

- [x] Add paired `MachineCNFRegression` files before the library. Preserve
  both initial missing-module failures in `ci-logs/issue624-machine-cnf-before-*`.
- [x] Reuse existing CNF implication and exactly-one proofs. Export the
  existing one-hot bounds instead of duplicating their derivations.
- [x] Compile every state/alphabet-symbol pair from the actual shared
  `Machine.instruction`, including ragged rows' default rejection.
- [x] Prove assignment-by-assignment correctness, constructive representation
  at arbitrary offsets, injectivity of instruction codes, wrong-instruction
  rejection, and correspondence to the original charged `step`.
- [x] Prove clause/variable/width bounds and polynomial bit length under the
  original unary `encodeCNF`.
- [x] Register 14 paired conclusions. Integrate regressions and source builds
  into `_CoqProject`, the local check script, and the existing workflow jobs.
- [x] Finish the full local Python/Lean/Rocq/Agda checks and manifest audits.
  `bash experiments/issue624/check.sh all` exits successfully, including the
  252-job Lean build and both 140-result assumption audits. The workflow also
  passes `actionlint` and its focused regression tests.
- [x] Review the paired source, regressions, integration, and existing PR diff.
  Re-run the completion preflight; the same 58 missing-result or explicit
  hardness-premise diagnostics remain.

Publication and fresh CI evidence are recorded in PR #630 after committing
this construction step. A passing local suite does not establish completion.

The negative regression selects exactly one state, one scanned symbol, and
one output instruction, yet deliberately selects rejection instead of the
required move. All three one-hot fragments pass; the compiled table clauses
reject it. This demonstrates the substantive dispatch constraint, rather
than only testing the existing exactly-one clauses. Other regressions cover
default rejection, missing/multiple values, an empty program, nonzero offsets,
distinct next states, and actual unary size.

All experiments have finite inputs. They do not deliberately stress memory
or stack. Large logs remain local under `ci-logs/`.

## Remaining enforced requirements

The checked dispatch compiler must still be wired to the selected head/tape
cell, next-row state/head/tape updates, certificate-dependent initial row,
row activity and final acceptance. The complete formula's extraction,
representation, satisfiability equivalence, and unary bit-size theorem remain
unproved. One input-independent finite single-tape reduction table must then
emit that formula with a charged polynomial `Computes` proof.

`satHard`, `cookLevin`, and the unconditional public P = NP bridges remain
unproved. Their existing premises remain explicit. The completion gate,
assumption policies and merge protection are preserved. PR #630 must stay
draft while these requirements fail.
