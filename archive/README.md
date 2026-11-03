# Archive

This directory keeps retired material for reference. **Nothing here is checked by CI**, and nothing here counts as a result of the repository. The current formal work is under `proofs/`, built on the shared model in [`proofs/complexity/`](../proofs/complexity/README.md), and is described in [FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md).

## `isabelle/`

Isabelle/HOL support was retired on 2026-01-19 (commit `f99742e`, issue [#530](https://github.com/konard/p-vs-np/issues/530)). The Isabelle CI job was removed; the workflow now carries the comment "Isabelle verification removed - proofs archived to ./archive/isabelle/". New formalizations use Lean 4 and Rocq, plus Agda for the shared-model files listed in CI.

The archive holds 97 `.thy` files:

- [`isabelle/proofs/`](isabelle/proofs/) mirrors the old `proofs/` layout: `basic/`, `p_eq_np/`, `p_not_equal_np/`, `p_vs_np_decidable/`, `p_vs_np_undecidable/`, `experiments/`, and `attempts/` (74 attempt folders).
- Ten attempt folders sit directly under [`isabelle/`](isabelle/): changlin-wan-2010-peqnp, guohun-zhu-2007-peqnp, han-xiao-wen-2010-peqnp, javaid-aslam-2008-peqnp, jerrald-meek-2008-pneqnp, jorma-jormakka-2008-pneqnp, lizhi-du-2010-peqnp, luigi-salemi-2009-peqnp, riaz-khiyal-2006-peqnp, and sergey-gubin-2010-peqnp.

These files use toy encodings that differ from the shared finite-machine model in [`proofs/complexity/`](../proofs/complexity/README.md). 69 of the 97 files contain `oops` or `sorry`. They were last checked before archiving and may no longer build with a current Isabelle release. Do not cite them as evidence for any result.

Issue [#627](https://github.com/konard/p-vs-np/issues/627) proposes moving the legacy Lean and Rocq toy frameworks ([`proofs/p_eq_np/`](../proofs/p_eq_np/README.md) and the `PvsNPProofAttempt` files in [`proofs/experiments/`](../proofs/experiments/README.md)) here as well. As of 2026-11-03 that has not happened.
