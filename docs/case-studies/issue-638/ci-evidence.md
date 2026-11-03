# CI evidence for the external re-verification

Key lines from the job logs of
[`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml).
Full logs are attached to each run as artifacts and are kept by GitHub for the
default retention period. Timestamps are UTC.

## Run [41548220250](https://github.com/konard/p-vs-np/actions/runs/41548220250) (commit `fdf2a3f`, 2026-11-02)

### `anthropic-eth`: **passed** ([job 125628945923](https://github.com/konard/p-vs-np/actions/runs/41548220250/job/125628945923))

```
identical: eth/MainResults.lean
identical: eth/Challenge.lean
identical: eth/comparator.json
identical: eth/lakefile.toml
identical: eth/lean-toolchain
warning: Challenge.lean:12:8: declaration uses `sorry`      # the challenge statements themselves
warning: Challenge.lean:16:8: declaration uses `sorry`
Build completed successfully (9768 jobs).                   # 23:50 → 00:19
'MainResults.ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainResults.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
project …/upstream/eth, toolchain leanprover/lean4:v4.33.1, configurations: comparator.json
Running nanoda kernel on solution                           # 00:22:06
nanoda kernel accepts the solution                          # 00:25:55
Your solution is okay!
PASS comparator.json
All 1 comparator configuration(s) accepted.
```

Tool pins printed by the upstream script: comparator `575674928e239f5bc452aab72d1dd7b0f1326494`,
nanoda_lib `68d5ca9db226849b41a6fff59d796ff19d0a8840`, landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.

### `anthropic-3sum-apsp`: **passed** ([job 125628945884](https://github.com/konard/p-vs-np/actions/runs/41548220250/job/125628945884))

```
identical: 3sum-apsp/EndStatement.lean
identical: 3sum-apsp/comparator-endstatement.json
identical: 3sum-apsp/comparator-paperstatements.json
identical: 3sum-apsp/lakefile.toml
identical: 3sum-apsp/lean-toolchain
Build completed successfully (3298 jobs).
'ThreeSumApsp.endStatement_theorem_19' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThreeSumApsp.endStatement_theorem_22_3SUM' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThreeSumApsp.endStatement_theorem_22_MinPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThreeSumApsp.endStatement_theorem_22_APSP' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThreeSumApsp.endStatement_corollary_39_zeroWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
… 137 declarations in total; 133 use exactly these three axioms and 4 a subset
(agreement_exactTriangle, agreement_minPlusProduct, agreement_rowByRow, figure_10_counts)
nanoda kernel accepts the solution
Your solution is okay!
PASS comparator-endstatement.json
nanoda kernel accepts the solution
Your solution is okay!
PASS comparator-paperstatements.json
All 2 comparator configuration(s) accepted.
```

### `openai-statement`: **failed because of a bug in our check** ([job 125628945716](https://github.com/konard/p-vs-np/actions/runs/41548220250/job/125628945716))

The statement elaborated. Lean printed its `sorryAx` dependency and the
expected warning:

```
warning: ComparatorChallenges/SubexponentialSAT.lean:194:8: declaration uses `sorry`
```

The check searched for `declaration uses 'sorry'` (with quotes). Lean v4.34
prints backticks, so the check failed. Commit `2381434` fixes the pattern
and requires that every `sorry` warning comes from the challenge file. As a
consequence, `openai-full` (`needs: openai-statement`) was skipped in this
run.

## Run [41553031734](https://github.com/konard/p-vs-np/actions/runs/41553031734) (commit `600a189`, 2026-11-03)

### `openai-statement`: **passed** ([job 125645069679](https://github.com/konard/p-vs-np/actions/runs/41553031734/job/125645069679))

```
identical: lean/ComparatorChallenges/SubexponentialSAT.lean
identical: lean/ComparatorChallenges/SubexponentialSAT.json
grep -qx 'leanprover/lean4:v4.34.1' upstream/lean/lean-toolchain
info: installing /home/runner/.elan/toolchains/leanprover--lean4---v4.34.1
info: mathlib: checking out revision 'd13f23b723b8a846827a245b89c10fc7d3f11612'
warning: ComparatorChallenges/SubexponentialSAT.lean:194:8: declaration uses `sorry`
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` is expected. The challenge file states the theorem and
leaves its proof as `sorry`, which the solution then fills. The check only
asks that the statement elaborates against the pinned Mathlib and that no
other file contributes a `sorry`.

### `anthropic-eth`: **passed again** ([job 125645070020](https://github.com/konard/p-vs-np/actions/runs/41553031734/job/125645070020))

The output is the same as in run 41548220250: five files identical,
`Build completed successfully (9768 jobs)`, `ethIsFalse` and `mainTheorem`
depend only on `[propext, Classical.choice, Quot.sound]`,
`nanoda kernel accepts the solution`, `Your solution is okay!`,
`All 1 comparator configuration(s) accepted.`

### `anthropic-3sum-apsp`: **passed again** ([job 125645069968](https://github.com/konard/p-vs-np/actions/runs/41553031734/job/125645069968))

The output is the same as in run 41548220250: five files identical,
`Build completed successfully (3298 jobs)`, nanoda accepts both
configurations, `PASS comparator-endstatement.json`,
`PASS comparator-paperstatements.json`,
`All 2 comparator configuration(s) accepted.`

### `openai-full`: **runner lost during the build** ([job 125646167760](https://github.com/konard/p-vs-np/actions/runs/41553031734/job/125646167760))

The pinned Mathlib cache was fetched (8908 files), and `lake build
OAI.Algorithms.SubexponentialSAT.Main` started at 00:35. At 03:07, 2 h 32 min
later and before the 300-minute step limit, GitHub stopped the runner:

```
/dev/root       145G   55G   91G  38% /          # before the build
2026-11-03T03:07:15Z ##[error]The runner has received a shutdown signal. …
2026-11-03T03:07:15Z ##[error]Process completed with exit code 143.
```

The steps marked `if: always()` (summary, log upload) were skipped because
the runner itself was gone. The build step only printed its output at the
end, so the log does not show how far the build got or why the runner
stopped. Disk space was not the cause (91 GB free). Memory exhaustion on the
16 GB runner is plausible, because OpenAI's README warns about memory
mapping limits, but this log cannot confirm it. This is **not** a build
error in OpenAI's proof.

The commit that records this run changes the job as follows:

* adds 32 GB of swap;
* prints memory, swap, disk and the last progress line every 5 minutes, so a
  lost runner still leaves evidence;
* stops the build cleanly at 280 minutes;
* caches `.lake/build`, so a later run resumes the build instead of starting
  again.
