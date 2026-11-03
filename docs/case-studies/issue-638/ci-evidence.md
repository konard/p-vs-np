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

## Run [41570704897](https://github.com/konard/p-vs-np/actions/runs/41570704897) (commit `42c986a`, 2026-11-03)

`openai-statement`, `anthropic-eth` and `anthropic-3sum-apsp` **passed** for
the third time, with the same key lines as above.

### `openai-full`: **build and axioms passed; Comparator stopped by a nanoda stack overflow** ([job 125703580857](https://github.com/konard/p-vs-np/actions/runs/41570704897/job/125703580857))

The build cache was empty, so the whole build ran (03:20 → 05:59). The
monitor added in `42c986a` shows why the previous runner was lost. Near the
end of the build, memory use reached 15.4 of 16 GB and swap use 15.7 GB:

```
[monitor 03:40] mem used 2744 of 15982 MB, available 13237 MB; swap used 1210 of 35839 MB; disk free 54G; ✔ [9517/12014] …
[monitor 04:40] mem used 8069 of 15982 MB, available 7912 MB; swap used 1927 of 35839 MB; disk free 41G; ✔ [11171/12014] …
[monitor 05:20] mem used 8239 of 15982 MB, available 7742 MB; swap used 7195 of 35839 MB; disk free 36G; ✔ [11876/12014] …
[monitor 05:40] mem used 15389 of 15982 MB, available 592 MB; swap used 15677 of 35839 MB; disk free 35G; ✔ [11995/12014] …
Build completed successfully (12014 jobs).                                           # 05:59:41
Cache saved with key: openai-build-4eaee87548250b2682affda7d05d947c05554bae-41570704897-1
```

`#print axioms` (step "Print axioms") and the build-time audits in `Final.lean`:

```
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.compiled_exact_count_and_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_eth' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sat_polynomial_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.original_sat_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Comparator (pins as in run 41548220250) built the challenge (8924 jobs) and
the solution (12014 jobs) in its sandbox, exported both, and ran the two
kernels:

```
Running nanoda kernel on solution                    # 06:07:46
thread 'main' (36906) has overflowed its stack       # 06:15:41
fatal runtime error: stack overflow, aborting
nanoda kernel rejected the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
uncaught exception: nanoda exited with 134
##[error]comparator did not accept comparator-subexponentialsat.json (exit status 1)
```

So **Lean's own kernel accepts the exported solution** against the trusted
challenge statement, under Comparator's sandbox and axiom whitelist. The
second kernel did not reach a verdict. Exit 134 is `SIGABRT` after a stack
overflow on the 8 MB default main-thread stack. That is a resource limit,
not a type error that nanoda found. Comparator still reports it as a
rejection, so the run counts as **not accepted**.

The commit that records this run raises the stack limit
(`ulimit -s unlimited`, inherited by comparator, landrun and nanoda) before
the Comparator step. The build cache saved above lets the next run skip the
3-hour build.

## Run [41591216557](https://github.com/konard/p-vs-np/actions/runs/41591216557) (commit `9aba41a`, 2026-11-03)

All four jobs **passed**:

| Job | Result |
|---|---|
| `openai-statement` ([job 125768147471](https://github.com/konard/p-vs-np/actions/runs/41591216557/job/125768147471)) | passed (fourth time) |
| `anthropic-eth` ([job 125768147752](https://github.com/konard/p-vs-np/actions/runs/41591216557/job/125768147752)) | passed (fourth time) |
| `anthropic-3sum-apsp` ([job 125768147829](https://github.com/konard/p-vs-np/actions/runs/41591216557/job/125768147829)) | passed (fourth time) |
| `openai-full` ([job 125768971029](https://github.com/konard/p-vs-np/actions/runs/41591216557/job/125768971029)) | **passed**: build, axioms, Comparator with nanoda |

### `openai-full`: **passed**

The build resumed from the cache saved by run 41570704897. Lake re-checked
the traces and rebuilt nothing. The axiom audit is the same as before:

```
Cache restored from key: openai-build-4eaee87548250b2682affda7d05d947c05554bae-41570704897-1
Build completed successfully (12014 jobs).                                   # 06:47:44
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Comparator, with the stack limit raised and nanoda forced on:

```
stack limit (KB): unlimited
== comparator @ 575674928e239f5bc452aab72d1dd7b0f1326494
== lean4export @ 076e8e57707e813375e8f9da8bf989799ace9680
== nanoda_lib @ 68d5ca9db226849b41a6fff59d796ff19d0a8840
== landrun @ 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
Build completed successfully (8924 jobs).     # challenge, inside the sandbox
Build completed successfully (12014 jobs).    # solution, inside the sandbox
Running nanoda kernel on solution             # 06:56:11
nanoda kernel accepts the solution            # 10:26:36 (3 h 30 min)
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
PASS comparator-subexponentialsat.json
All 1 comparator configuration(s) accepted.
```

So `openai/math@4eaee87` passes the same check as Anthropic's projects:

* `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` has
  the type of the trusted challenge statement (byte-identical to
  [`sources/openai-math`](sources/openai-math/));
* it uses only the three standard axioms;
* two independent kernels accept it.

The workflow file at this commit is the same as on the PR head. Later commits
change only the case-study documents, which do not trigger this workflow.
