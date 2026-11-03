# Planned issues for issue #638 (executed in PR #639)

The issue asks to "plan issues to test for all of these ideas" and to "plan
and execute everything in this single pull request". So each idea below is
written as an issue draft (goal, acceptance criteria, method), then executed
in PR #639, with its verdict and evidence. Items that could not be completed
are marked **blocked**, **not done** or **open**, with the reason, and are not
presented as done. Each of them has a follow-up GitHub issue: #642 (P6
general bound), #643 (P8), #644 (P9), #645 (P12). PR #639 therefore refers to
#638 without closing it.

Names of theorems refer to
[`proofs/experiments/issue638/lean/ETH.lean`](../../../proofs/experiments/issue638/lean/ETH.lean)
and [`rocq/ETH.v`](../../../proofs/experiments/issue638/rocq/ETH.v). "Certified"
means listed in [`scripts/proof_status.json`](../../../scripts/proof_status.json)
and checked by `scripts/check_proof_status.py` in CI.

---

## P1. ETH implies P ≠ NP

* **Goal.** Prove formally that the repository's `ETH` implies its
  `PNotEqualsNP`, so that ETH-based arguments are known to be *at least as
  strong as* P ≠ NP.
* **Acceptance criteria.** Lean and Rocq theorems with the displayed statement
  `ETH → PNotEqualsNP` over `Complexity.Machine`, no `sorry`/`Admitted`, no
  axioms beyond Lean's standard three, listed in `proof_status.json`.
* **Method.** Contrapositive. `P = NP` puts SAT in P (`SATVerifier.satInNP`).
  A polynomial bound is `O*(2^{n/d})` for every `d`
  (`Idea41.poly_le_two_pow`, `ksatExpTime_of_inP_sat`), so `¬ ETH`
  (`not_eth_of_pEqualsNP`).
* **Verdict.** **Proved** (certified): `pNotEqualsNP_of_eth`,
  `not_eth_of_pEqualsNP`.
* **Evidence.** `verification.yml` (Lean build, Rocq compile, proof-status
  audit); [`print_axioms.txt`](../../../experiments/issue638/results/print_axioms.txt).

## P2. SETH implies P ≠ NP

* **Goal.** Same as P1 for SETH.
* **Acceptance criteria.** As P1, for `SETH → PNotEqualsNP`.
* **Method.** If `P = NP`, every `k` has a polynomial-time k-SAT decider, which
  is within `O*(2^{(1−1/d)n})` for all `d`.
* **Verdict.** **Proved** (certified): `pNotEqualsNP_of_seth`,
  `not_seth_of_pEqualsNP`.
* **Evidence.** As P1.

## P3. Does refuting ETH give P = NP?

* **Goal.** Decide whether the October 2026 claims, if correct, affect the
  P vs NP question directly.
* **Acceptance criteria.** Either a formal proof that a subexponential
  algorithm gives a polynomial one, or a formal example of a budget that is
  subexponential but not polynomial.
* **Method.** Exhibit `logBudget n = 2^{⌊n/(⌊log₂ n⌋+1)⌋}`. Prove that it is
  below `C_d · 2^{n/d}` for every `d > 0`, and that it is not polynomially
  bounded. Also prove that a decider within `logBudget` already gives
  `SubexpKSAT k` (`subexpKSAT_of_logBudget`), so it refutes ETH
  (`eth_iff_not_subexp3`).
* **Verdict.** **Not derivable from the bound alone.** A subexponential
  *upper bound* does not give a polynomial one (`logBudget_gap`,
  `logBudget_not_polynomial`, certified). Whether ¬ETH implies P = NP is
  open; it is trivially true if P = NP. Disproving the implication would mean
  proving ¬ETH ∧ P ≠ NP, which includes a proof of P ≠ NP. The labs' *time
  bounds* `2^{Θ(n·polyloglog n/√log n)}` are superpolynomial too (informal
  remark); the true running time of their algorithms is not known.
  `subexpKSAT_of_logBudget` shows that a decider within `logBudget` would
  already refute ETH.
* **Evidence.** As P1.

## P4. Re-verify Anthropic's ETH refutation

* **Goal.** Rebuild `anthropics/formal-math/eth` at the pinned commit, without
  trusting upstream CI and without using the development machine.
* **Acceptance criteria.**
  1. The trusted files (`MainResults.lean`, `Challenge.lean`, `comparator.json`,
     `lakefile.toml`, `lean-toolchain`) are
     byte-identical to [`sources/anthropic-formal-math-eth`](sources/anthropic-formal-math-eth/).
  2. `lake build` succeeds with the upstream toolchain (v4.33.1).
  3. `#print axioms` on `ethIsFalse` and `mainTheorem` shows only `propext`,
     `Classical.choice`, `Quot.sound`. This runs upstream's
     `scripts/PrintAxioms.lean` inside the built project, so it is a
     convenience. Criterion 4 is the check that does not trust the build.
  4. Comparator (lean4export + nanoda + landrun) prints
     `Your solution is okay!`.
* **Method.** Job `anthropic-eth` of
  [`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml).
* **Verdict.** See [Re-verification status](README.md#re-verification-status).
* **Fidelity.** [`fidelity-audit.md`](fidelity-audit.md) §2: faithful, slightly
  stronger than the textbook ETH.

## P5. Re-verify OpenAI's ETH refutation

* **Goal.** Check `openai/math` family 378 at the pinned commit.
* **Acceptance criteria.**
  1. *Must pass:* the challenge files are byte-identical to
     [`sources/openai-math`](sources/openai-math/). The toolchain (v4.34.1) and
     Mathlib (`d13f23b`) pins match. The challenge statement elaborates, and
     its only `sorry` is the challenge theorem itself.
  2. *Best effort:* `lake build OAI.Algorithms.SubexponentialSAT.Main` (12014
     build jobs). `#print axioms` shows no `sorryAx`. Comparator accepts the
     solution with nanoda forced on, which upstream leaves off.
* **Method.** Jobs `openai-statement` and `openai-full`.
* **Verdict.** **Both criteria passed** (runs
  [41591216557](https://github.com/konard/p-vs-np/actions/runs/41591216557)
  and [41619710887](https://github.com/konard/p-vs-np/actions/runs/41619710887),
  and the dispatched run [41695515133](https://github.com/konard/p-vs-np/actions/runs/41695515133) on head `934d5b8` (later commits change only `docs/`),
  see [Re-verification status](README.md#re-verification-status) and
  [`ci-evidence.md`](ci-evidence.md)). The best-effort part needed three
  attempts. The first lost its runner (memory). The second built the
  solution with swap and had clean axioms, but nanoda overflowed its stack.
  The third raised the stack limit, and nanoda and Lean's kernel both
  accepted.
* **Fidelity.** [`fidelity-audit.md`](fidelity-audit.md) §3: faithful, with a
  weaker exponent than the paper and no Lean statement of ETH itself.

## P6. The paper's eight-square identity, and the README hint's rank bound

* **Goal.** Check independently the algebra behind Anthropic's algorithm.
  The paper (`eth/paper.pdf` at
  [`16a5ce4`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/paper.pdf),
  §2.4, Lemma 2, Appendix F) builds on the **eight-square identity**
  (Degen 1818, Graves 1843): eq. (12), a statement about 12 bits, with the
  gain ρ = 11/12; eq. (28) is its cancellation. Separately, the upstream
  README's "condensed form interpretable by AI models" uses the textbook
  fact `SWAP = I − 2·singlet` on one bit position, expands it over `λ`
  positions into a signed sum of operators `O_j`, and bounds
  row rank × column rank by `12^λ`. By the README's own words, the condensed
  form rederives only `O(2^{δn})` for every δ, not the published algorithm.
* **Acceptance criteria.** Eq. (12) and eq. (28) proved in Lean and Rocq over
  all settings. The hint's identity proved. The hint's rank bound checked
  exactly over ℚ for small `λ`.
* **Method.** `decide` over all 4096 settings of the 12 bits
  (`eightSquare`, `eightSquare_cancel`). `decide` on integer 4×4 matrices
  (`swap_eq_id_sub_singlet`, `singlet_sq`, `swap_sq`). Fraction-free
  (Bareiss) elimination over ℤ, which gives exact ranks over ℚ, in
  [`swap_singlet_ranks.py`](../../../experiments/issue638/swap_singlet_ranks.py)
  for `λ ≤ 4`.
* **Verdict.**
  * Eq. (12) and eq. (28): **proved** (certified).
  * `SWAP = I − 2·singlet`: **proved** (certified). This is a textbook 4×4
    fact. It is kept, but it is not evidence about the algorithm.
  * Rank bound of the hint: **checked for λ ≤ 4 only**, exactly over ℚ,
    under one reading of "row rank" and "column rank" (two cuts of the
    rectangle; see the script's docstring). The largest product is 4489
    against `12^4 = 20736`
    ([output](../../../experiments/issue638/results/swap_singlet_ranks.txt)).
  * The general bound for every `λ` is **open** here (follow-up
    [#642](https://github.com/konard/p-vs-np/issues/642)). Anthropic's Lean
    proof, re-verified in P4, covers the algorithm as a whole.

## P7. 3SUM and APSP hypotheses refuted (Anthropic `3sum-apsp`)

* **Goal.** Re-verify the Lean proof of truly subquadratic 3SUM and
  subcubic APSP. These are the other fine-grained hypotheses refuted in the
  window.
* **Acceptance criteria.** The same four criteria as P4, for both Comparator
  configurations of `3sum-apsp`.
* **Method.** Job `anthropic-3sum-apsp`.
* **Verdict.** See [Re-verification status](README.md#re-verification-status).
  **Relevance.** These hypotheses concern polynomial exponents. They do not
  bear on P vs NP, and no repository document depends on them.

## P8. Transfer the lab theorems into `Complexity.Machine`

* **Goal.** Turn the named hypothesis `SubexpKSAT 3` into a theorem of this
  repository, so that `¬ ETH` and `¬ SETH` become certified results here.
* **Acceptance criteria.** A Lean proof (and a Rocq counterpart, by the
  repository's rule) that Mathlib `TM2` machines, or OpenAI's
  `PrimitiveMachine`, are simulated by `Complexity.Machine` with polynomial
  overhead. Plus a polynomial translation from `encClauses` /
  `Encoding.encodeCNF` to our `encodeCNF`. Plus `runtimeScale n = o(n)` for
  OpenAI's bound.
* **Method (proposed).** (a) Add Mathlib to a separate Lake package that
  depends on both the lab project and this repository, and prove the
  simulation there. (b) Alternatively, re-state TM2 semantics without Mathlib.
  Components: Mathlib `Turing`, CSLib, the Cook–Levin mechanizations (see
  [README](README.md#existing-components-and-libraries)).
* **Verdict.** **Blocked.** This repository does not depend on Mathlib. The
  two labs use different Lean and Mathlib versions (v4.33.1 and v4.34.1), so
  one package cannot import both without porting. A multi-tape simulation
  with time bounds, done in both Lean and Rocq, is a large engineering task
  that exceeds this PR. `SubexpKSAT 3` stays a named hypothesis. Follow-up:
  [#643](https://github.com/konard/p-vs-np/issues/643).

## P9. SETH implies ETH (sparsification)

* **Goal.** Prove `SETH → ETH` formally, as in Impagliazzo–Paturi–Zane.
* **Acceptance criteria.** Lean and Rocq proofs of the sparsification lemma
  over our CNF type and machine model.
* **Method (proposed).** Port Anthropic's
  [`eth/proof/sparsification/`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification)
  (Mathlib) to the repository's types. The algorithmic part also needs P8's
  machine-level reasoning.
* **Verdict.** **Not done** (it depends on P8). It is not needed for the
  issue's conclusions: `not_seth_of_subexpAllK` refutes SETH directly from
  the shape of the claims, without sparsification. Follow-up:
  [#644](https://github.com/konard/p-vs-np/issues/644).

## P10. Other AI-lab results in theoretical computer science

* **Goal.** Make sure that no other result in the window settles or changes
  P vs NP.
* **Acceptance criteria.** Every TCS result found in the survey is listed with
  its formal artifact and a relevance verdict.
* **Method.** Primary sources (`openai/math` [`CONTENTS.md`](sources/openai-math/CONTENTS.md),
  `anthropics/formal-math`, arXiv) and secondary press coverage.
* **Verdict.** **Recorded** in the [catalog](README.md#catalog-of-ai-lab-results-2025-10-13--2026-11-02).
  None claims P = NP or P ≠ NP. The restricted-model lower bounds (families
  108, 112, 126, 133, 135) are of the kinds covered by the barriers studied in
  `proofs/experiments/issue609`. Rebuilding their Lean proofs is out of scope.

## P11. Repository documents that rely on ETH or SETH

* **Goal.** Prevent conclusions that rest on a hypothesis that may now be
  false.
* **Acceptance criteria.** Every place where ETH or SETH is used as evidence
  or as an assumption carries a dated note. No certified theorem assumes ETH
  or SETH.
* **Method.** Search for `ETH`, `SETH` and `Exponential Time` across the
  repository's documents and `proof_status.json`.
* **Verdict.** **Done.** The notes were added to the files listed under
  [Impact](README.md#impact-on-this-repository). The first pass missed three
  attempts, found in review: Mimouni 2006 (whose Lean and Rocq refutations
  use an `exponential_time_hypothesis` that actually asserts Clique ∉ P),
  Chaudhari 2009 (ETH called "well-established") and Akbari 2008 (SETH).
  They now carry notes too. No entry of `proof_status.json` assumes ETH or
  SETH.

## P12. `E^NP` circuit lower bound from the ETH algorithm

* **Goal.** Check the second claim of both labs (Anthropic's paper §1 and §7;
  OpenAI's family 378): by Williams' "algorithms imply
  lower bounds" connection, the counting algorithm gives superlinear circuit
  lower bounds for a language in `E^NP`.
* **Acceptance criteria.** A formal statement and proof, or a documented
  reason why the claim is out of reach.
* **Method.** Read the scope document
  [`378.md`](sources/openai-math/lean/docs/378.md).
* **Verdict.** **Open; informal only.** OpenAI's Lean scope covers only the
  counting algorithm. Formalizing Williams' framework (nondeterministic time
  hierarchy, succinct SAT) is a project of its own. It is the most relevant
  follow-up for P ≠ NP research, because circuit lower bounds are the
  classical route to it. Even so, superlinear bounds for `E^NP` are far from
  `NP ⊄ P/poly`. Follow-up:
  [#645](https://github.com/konard/p-vs-np/issues/645).
