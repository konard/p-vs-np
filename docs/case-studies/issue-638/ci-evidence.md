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
