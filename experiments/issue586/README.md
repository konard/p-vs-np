# Weiss growth regression

Run `bash experiments/issue586/check.sh` from the repository root. It builds
the Lean refutation, verifies the concrete counterexample to the old witness,
and prints the axiom dependencies of the four counting theorems. The check
fails if any of those dependencies contains `sorryAx`.

Before the fix, `c = 1`, `k = 10`, and the old choice `n = c + k + 2 = 13`
required `2^13 > 13^10`, which is false. The check printed `sorryAx` for
`numAssignments_exponential`, `ke_branches_still_exponential`, and
`weiss_approach_fails`.

The repaired theorem takes `m = c + k + 8` and `n = 2^m`. Its proof shows
`c + m*k < m² ≤ 2^m`, which is enough to establish
`c*n^k ≤ 2^(c+m*k) < 2^n`. The
downstream theorems now state only assignment counts and full cut-tree
counts; a KE algorithm lower bound requires an additional premise.
