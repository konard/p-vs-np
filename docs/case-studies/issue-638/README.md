# Case study: issue #638: ETH and the latest AI-lab results

> Issue: [#638 "Exponential Time Hypothesis (ETH) and all latest published developments by AI labs"](https://github.com/konard/p-vs-np/issues/638)
> Pull request: [#639](https://github.com/konard/p-vs-np/pull/639)
> Window covered: **2025-10-13** (first commit of this repository) to **2026-11-02**.

## Bottom line

* On **26–27 October 2026** OpenAI and Anthropic independently published
  claims that **the Exponential Time Hypothesis (ETH) is false**. Each comes with
  a Lean 4 proof of a deterministic algorithm that counts the satisfying
  assignments of a k-CNF in time `2^{O_k(n · polyloglog n / √log n)}`. Neither
  is peer reviewed. The ETH authors (Impagliazzo, Paturi) and Ryan Williams
  are reviewing OpenAI's proof and state that their involvement "should not be
  taken as certification".
* **What this repository proves (Lean and Rocq, in `scripts/proof_status.json`):**
  ETH ⇒ P ≠ NP, SETH ⇒ P ≠ NP, a subexponential k-SAT algorithm refutes ETH
  (and SETH if it covers every k), and **refuting ETH does not imply P = NP**:
  there are budgets below every `2^{δn}` that are still superpolynomial. See
  [`proofs/experiments/issue638`](../../../proofs/experiments/issue638/README.md).
* **Consequence for our P vs NP research.** If the claims stand, `P ≠ NP`
  loses ETH and SETH as supporting hypotheses. These are *stronger* than
  `P ≠ NP`, and none of the repository's main results assume them. `P vs NP`
  itself stays open in both directions. Repository documents that cite ETH/SETH
  as evidence now carry a dated status note (see [Impact](#impact-on-this-repository)).
* **Independent re-verification.** This happens on GitHub runners, not on the
  development machine, in
  [`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml).
  The status of each job is recorded in [Re-verification status](#re-verification-status).
  The external proofs are **not** "certified" results of this repository.

## Contents of this folder

| File | Purpose |
|---|---|
| [`README.md`](README.md) | This analysis: requirements, timeline, catalog, verdicts, tools |
| [`planned-issues.md`](planned-issues.md) | One issue draft per idea, with test plan, verdict and evidence (executed in PR #639) |
| [`fidelity-audit.md`](fidelity-audit.md) | Line-by-line comparison of the labs' Lean statements with the textbook ETH |
| [`ci-evidence.md`](ci-evidence.md) | Key lines of the CI logs of the external re-verification runs |
| [`sources/`](sources/) | Byte-identical copies of the trusted upstream statement files at pinned commits (see `COMMIT.txt` in each folder) |

Each `sources/` folder keeps the upstream licence notice (`NOTICE`, Apache-2.0
for Anthropic). The OpenAI files are excerpts kept for audit.

## Requirements of the issue and how each is met

| # | Requirement (from the issue text) | Plan | Evidence in this PR | Status |
|---|---|---|---|---|
| R1 | "Double check all relevant research results … published by AI labs … recently (from the moment we started the initial research)" | Survey OpenAI, Anthropic, Google DeepMind and others from 2025-10-13. Read primary sources (repositories, arXiv) and record secondary ones as secondary. | [Catalog](#catalog-of-ai-lab-results-2025-10-13--2026-11-02), [timeline](#timeline), [`sources/`](sources/) | done |
| R2 | "find all new relevant ideas, and plan issues to test for all of these ideas" | One idea per claim or technique that touches P vs NP. Each gets an issue draft with acceptance criteria. | [`planned-issues.md`](planned-issues.md) (P1–P12) | done (drafts; executed here, not opened as separate issues, because the issue asks for one PR) |
| R3 | "either prove or disprove any relevant idea using formal provers" | Prove the logical links in Lean **and** Rocq over the shared machine model. Re-check the labs' own Lean proofs with their pinned toolchains, `#print axioms` and Comparator. | 13 Lean + 13 Rocq theorems in `scripts/proof_status.json`; [`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml) | done for P1–P3, P6 (identity), P11; CI for P4, P5, P7; **blocked**: P8 (model transfer), P9 (sparsification) — see [blocked items](#uncertainties-and-blocked-items) |
| R4 | "independently reverify … use CI/CD … do not overload our local development machine" | Separate workflow, pinned commits, byte-identical statement check against `sources/`, upstream toolchains, Comparator with the independent `nanoda` kernel. Only light checks run locally. | workflow + [status](#re-verification-status) | see status table |
| R5 | "collect data … compile that data to `./docs/case-studies/issue-{id}` … deep case study analysis … search online … list of each and all requirements … propose possible solutions … check known existing components/libraries" | This folder. | this README, [`fidelity-audit.md`](fidelity-audit.md), [tools survey](#existing-components-and-libraries) | done |
| R6 | "plan and execute everything in this single pull request" | All of the above in PR #639 | PR #639 | done |

## Timeline

| Date (2025–2026) | Event | Source |
|---|---|---|
| 2025-09 | Aaronson–Witteveen, *Limits to black-box amplification in QMA*. GPT-5 suggested a key step. Just before the window; listed for completeness. | [arXiv:2509.21131](https://arxiv.org/abs/2509.21131) |
| 2025-09 / later revisions | Nagda–Raghavan–Thakurta: AlphaEvolve finds gadgets giving NP-hardness of MAX-4-CUT within 0.987, plus Ramanujan-graph certificates | [arXiv:2509.18057](https://arxiv.org/abs/2509.18057), [Google Research blog](https://research.google/blog/ai-as-a-research-partner-advancing-theoretical-computer-science-with-alphaevolve/) |
| 2025-10-13 | First commit of this repository: start of the window | `git log` |
| 2026-02 | Google, *Accelerating Scientific Research with Gemini: Case Studies and Common Techniques* | [arXiv:2602.03837](https://arxiv.org/abs/2602.03837) |
| 2026-05 | DeepMind AlphaProof Nexus: Lean agent; 9 Erdős problems, 44 OEIS conjectures | [arXiv:2605.22763](https://arxiv.org/abs/2605.22763) |
| 2026-08-10…28 | Anthropic `formal-math/zeta23` (Alpöge–Furman, >2/3 of ζ zeros simple and on the line), Palomar layout | [anthropics/formal-math](https://github.com/anthropics/formal-math) |
| 2026-08-17 | AlphaEvolve-assisted ω < 2.371177 | [arXiv:2608.16884](https://arxiv.org/abs/2608.16884) |
| 2026-10-06 | OpenAI releases 721 manuscripts in 373 families (`openai/math`), including UGC, L = RL = BPL, ω ≤ 9/4, a quasilinear PCP for PPAD | [`sources/openai-math/README.md`](sources/openai-math/README.md), [`CONTENTS.md`](sources/openai-math/CONTENTS.md) |
| 2026-10-06 | Anthropic `formal-math/3sum-apsp`: Lean proof of Alman–Vassilevska Williams, truly subquadratic 3SUM and subcubic APSP | [arXiv:2610.06783](https://arxiv.org/abs/2610.06783), [`sources/anthropic-formal-math-3sum-apsp`](sources/anthropic-formal-math-3sum-apsp/) |
| 2026-10-07 | OpenAI withdraws 3 manuscripts (sign error in a Hodge paper) and revises 14 | [`sources/openai-math/history.md`](sources/openai-math/history.md), [Retraction Watch](https://retractionwatch.com/2026/10/08/openai-withdraws-preprints-722-manuscripts-unsolved-math-problems/), [AHM statement via T. Tao](https://terrytao.wordpress.com/2026/10/07/ahm-statement-on-openais-october-6-release-of-mathematical-documents/) |
| 2026-10 (after 10-06) | Follow-ups to 3SUM/APSP: a simplified proof; k-SUM hypothesis refuted for odd k; real 3SUM/APSP derandomized | [arXiv:2610.15663](https://arxiv.org/abs/2610.15663), [arXiv:2610.42012](https://arxiv.org/abs/2610.42012) |
| 2026-10-16 | Both labs report that their internal models found the ETH algorithm on this date (Anthropic: "internal research Claude model", reported 14M output tokens, no human input) | lab statements as reported by [Washington Times](https://www.washingtontimes.com/news/2026/oct/27/openai-says-model-refuted-exponential-time-hypothesis/), [lilting.ch](https://lilting.ch/en/articles/eth-exponential-time-hypothesis-refuted-openai-anthropic) (secondary) |
| 2026-10-17 | OpenAI: Lean formalization completed | same (secondary) |
| 2026-10-26 21:18 UTC | `openai/math` commit `7ef5c0c` adds *The Exponential Time Hypothesis is False* (family 378) with Lean; review group Impagliazzo–Paturi–Williams announced | [`sources/openai-math/history.md`](sources/openai-math/history.md) |
| 2026-10-27 03:07 UTC | `anthropics/formal-math` commit `16a5ce4` adds `eth/`: *A 2^o(n) Time Algorithm for 3-SAT* by Claude, with Lean | [`sources/anthropic-formal-math-eth`](sources/anthropic-formal-math-eth/) |
| 2026-10-27 | R. Williams: "An internal model at OpenAI has produced a **claimed** refutation of ETH". OpenAI reportedly funds an independent review (reported $5M) | [dealroom (secondary)](https://dealroom.co/news/167089-openai-says-its-ai-disproved-a-core-computer-science-assumption-gives-5m/) |
| 2026-10-30 00:35 UTC | `openai/math` `4eaee87` (the commit pinned here): Comparator fix for an unrelated Hodge result | [`sources/openai-math/COMMIT.txt`](sources/openai-math/COMMIT.txt) |
| 2026-11-02 | This case study; both pinned commits are still the latest upstream commits | `gh api …/commits` |

OpenAI's blog post on the review
(`openai.com/index/building-scientific-understanding-with-academic-communities/`)
returned HTTP 403 to automated fetches. Its content is cited only through the
secondary sources above, and the dates attributed to it are marked secondary.

## Catalog of AI-lab results (2025-10-13 → 2026-11-02)

Relevance is judged against this repository's question (P vs NP) and its
toolbox (the shared machine model, SAT, reductions, barriers).

| Lab | Result | Formal artifact | Relevance to P vs NP | Verdict here |
|---|---|---|---|---|
| OpenAI | **ETH is false**: deterministic #k-SAT in `(L+1)^{O_k(1)}·2^{O_k(n(loglog n)²/√log n)}` with polynomial space (family 378) | Lean, `openai/math` `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`; Comparator challenge [`SubexponentialSAT.lean`](sources/openai-math/lean/ComparatorChallenges/SubexponentialSAT.lean) | **High.** It removes a hypothesis stronger than P ≠ NP. It does not decide P vs NP (proved: `logBudget_gap`). | statement elaborated in CI; full build best effort (P5) |
| OpenAI | same family: superlinear circuit lower bounds for a language in `E^NP` on infinitely many lengths (Williams' "algorithms ⇒ lower bounds") | **not formalized** ([scope](sources/openai-math/lean/docs/378.md) covers only the counting algorithm) | **High in principle**: circuit lower bounds are the classical route to P ≠ NP, but superlinear bounds for `E^NP` are far from it | recorded as P12; informal only |
| Anthropic | **ETH is false**: one TM counts k-CNF models in `2^{C·min(km/√lg m, k²n·lg lg n/√lg n)}` | Lean, `anthropics/formal-math/eth`, `MainResults.ethIsFalse`, `MainResults.mainTheorem`; Comparator + nanoda in upstream CI | **High**, same as above. Stronger statement: one machine for all k, no polynomial factor. | rebuilt in CI (P4) |
| Anthropic | 3SUM in `n^{1.9992}`, APSP and (min,+) in `n^{2.99942}`, Exact Triangle, Zero-Weight k-Clique on a word RAM (Alman–Vassilevska Williams) | Lean, `formal-math/3sum-apsp` [`EndStatement.lean`](sources/anthropic-formal-math-3sum-apsp/EndStatement.lean) | **Medium.** Refutes the 3SUM and APSP hypotheses of fine-grained complexity, but these are polynomial-time questions, not P vs NP. | rebuilt in CI (P7) |
| OpenAI | UGC (102), L = RL = BPL (103), 3-colorable coloring hardness (106), ω ≤ 9/4 (107), permanent–determinant `Ω(n³)` (108), depth-3 circuits (112), SDP lifts of matching (126), WL lower bounds (133), depth-5 IMM (135), PCP for PPAD (136), sensitivity-type disproof (192), random k-SAT thresholds (235), choiceless polynomial time (243) | Lean for all of these except 136 ([`CONTENTS.md`](sources/openai-math/CONTENTS.md)) | **Medium to low.** None claims P = NP or P ≠ NP. Several are lower bounds in restricted models, which fall under the barriers in `proofs/experiments/issue609`. | recorded (P10); not rebuilt, out of scope beyond the catalog |
| Google DeepMind | AlphaEvolve: ω < 2.371177; MAX-4-CUT 0.987 hardness gadgets; Ramanujan certificates | rational-arithmetic certificates, gadget verifiers (not Lean) | **Low to medium.** These are better constants for known theorems. | recorded (P10) |
| Google DeepMind | AlphaProof Nexus (Erdős, OEIS); Gemini case studies | Lean (Nexus) | **Low**: combinatorics and number theory | recorded |
| OpenAI (GPT-5 assisted) | Aaronson–Witteveen QMA amplification limit (oracle result) | none | **Low**: relativized quantum complexity; just before the window | recorded |

No AI-lab result in the window claims to settle P vs NP. The
ETH claims are the only results that change the status of a hypothesis this
repository discusses as supporting evidence.

## Ideas and verdicts

Every idea is written out as an issue draft with acceptance criteria and
evidence in [`planned-issues.md`](planned-issues.md). Summary:

| # | Idea | Method | Verdict |
|---|---|---|---|
| P1 | ETH ⇒ P ≠ NP | Lean + Rocq `pNotEqualsNP_of_eth` | **proved** |
| P2 | SETH ⇒ P ≠ NP | Lean + Rocq `pNotEqualsNP_of_seth` | **proved** |
| P3 | ¬ETH ⇒ P = NP? | Lean + Rocq `logBudget_gap` | **disproved as an inference**: a subexponential bound does not give a polynomial one. P vs NP stays open. |
| P4 | Anthropic's ETH refutation re-checks | CI rebuild, `#print axioms`, Comparator + nanoda | see [status](#re-verification-status) |
| P5 | OpenAI's ETH refutation re-checks | CI: statement elaboration (must pass), full build (best effort) | see [status](#re-verification-status) |
| P6 | Anthropic's key identity `SWAP = I − 2·singlet` and rank bound `≤ 12^λ` | Lean + Rocq `decide` for the identity; exact rank computation for `λ ≤ 4` | identity **proved**; rank bound **checked for λ ≤ 4 only** |
| P7 | 3SUM / APSP hypotheses refuted | CI rebuild of `3sum-apsp` | see [status](#re-verification-status) |
| P8 | Transfer of the lab theorems to `Complexity.Machine` | needs Mathlib TM2 / PrimitiveMachine simulation | **blocked** (no Mathlib in this repository; large engineering task) |
| P9 | SETH ⇒ ETH (sparsification) | formalization of IPZ sparsification | **not done**; existing component in Anthropic `eth/` |
| P10 | Other AI-lab TCS results | catalog + relevance | recorded; none settles P vs NP |
| P11 | Repository documents that rely on ETH/SETH | audit + dated notes | **done** |
| P12 | `E^NP` circuit lower bound from the ETH algorithm | informal; not formalized upstream | open; recorded |

## Re-verification status

Jobs of [`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml)
(GitHub-hosted `ubuntu-latest`, 4 vCPU / 16 GB). The table is updated with the
last run on this PR.

| Job | What it checks | Result |
|---|---|---|
| `anthropic-eth` | trusted files byte-identical to `sources/`; `lake build`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; Comparator (lean4export + nanoda + landrun) prints `Your solution is okay!` | **passed** in runs [41548220250](https://github.com/konard/p-vs-np/actions/runs/41548220250), [41553031734](https://github.com/konard/p-vs-np/actions/runs/41553031734) and [41570704897](https://github.com/konard/p-vs-np/actions/runs/41570704897): 9768 build jobs, `ethIsFalse` and `mainTheorem` use only the three standard axioms, nanoda accepts, Comparator `Your solution is okay!` ([evidence](ci-evidence.md)) |
| `anthropic-3sum-apsp` | same, for both Comparator configurations | **passed** in runs [41548220250](https://github.com/konard/p-vs-np/actions/runs/41548220250), [41553031734](https://github.com/konard/p-vs-np/actions/runs/41553031734) and [41570704897](https://github.com/konard/p-vs-np/actions/runs/41570704897): 3298 build jobs, 137 declarations with standard axioms only, both configurations accepted by Comparator and nanoda ([evidence](ci-evidence.md)) |
| `openai-statement` | trusted challenge files byte-identical; toolchain v4.34.1 and Mathlib `d13f23b` pinned; the challenge statement elaborates; its only `sorry` is the challenge itself | **passed** in runs [41553031734](https://github.com/konard/p-vs-np/actions/runs/41553031734) and [41570704897](https://github.com/konard/p-vs-np/actions/runs/41570704897): files identical, pins match, the only `sorry` warning is `SubexponentialSAT.lean:194:8` (the challenge theorem) ([evidence](ci-evidence.md)) |
| `openai-full` | `lake build OAI.Algorithms.SubexponentialSAT.Main` (~4000 files), no `sorryAx`, Comparator | run [41553031734](https://github.com/konard/p-vs-np/actions/runs/41553031734): the runner was lost after 2 h 32 min of building (`received a shutdown signal`), not a build error ([evidence](ci-evidence.md)); retried with swap, monitoring and a resumable build cache. Run [41570704897](https://github.com/konard/p-vs-np/actions/runs/41570704897): **build passed** (12014 jobs, peak 15.4 GB RAM + 15.7 GB swap) and `exact_count_and_sat` uses only the three standard axioms; in Comparator **Lean's kernel accepts** the solution but **nanoda overflowed its 8 MB stack** (exit 134), so Comparator did not accept ([evidence](ci-evidence.md)). Retry with unlimited stack: _pending_. |

Even when all jobs pass, the result means "the Lean kernels and Comparator
accept these proofs of these statements". Whether the statements mean ETH
is a separate question, examined in [`fidelity-audit.md`](fidelity-audit.md).
The labs' theorems remain **external** and are not entries of
`scripts/proof_status.json`.

## Impact on this repository

ETH and SETH appear in the repository as *evidence for* P ≠ NP or as
conditional hardness assumptions. Each place below now carries a dated note.
The note says that ETH and SETH are claimed refuted, that the claim is
unreviewed, that the hypotheses are strictly stronger than P ≠ NP (P1, P2),
and that P vs NP is unaffected (P3):

* [`SOLUTION_STRATEGIES.md`](../../../SOLUTION_STRATEGIES.md)
* [`P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md`](../../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md)
* [`TOOLS_AND_METHODOLOGIES.md`](../../../TOOLS_AND_METHODOLOGIES.md)
* issue #532 idea notes [Idea01](../../../proofs/experiments/issue532/ideas/Idea01.md),
  [Idea17](../../../proofs/experiments/issue532/ideas/Idea17.md),
  [Idea25](../../../proofs/experiments/issue532/ideas/Idea25.md),
  [Idea26](../../../proofs/experiments/issue532/ideas/Idea26.md),
  [Idea37](../../../proofs/experiments/issue532/ideas/Idea37.md),
  [Idea41](../../../proofs/experiments/issue532/ideas/Idea41.md)

No certified theorem in `scripts/proof_status.json` assumes ETH or SETH, so no
certified result changes.

## Existing components and libraries

| Component | What it offers | Use here |
|---|---|---|
| [Mathlib `Turing` (TM0/TM1/TM2, `TM2ComputableInTime`)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TMComputable.html) | Turing machines with time bounds; Anthropic's model | Target or source of the P8 simulation |
| [leanprover/comparator](https://github.com/leanprover/comparator) | Checks that a solution proves exactly the challenge statement, using only permitted axioms | CI (P4, P5, P7) |
| [nanoda_lib](https://github.com/robsimmons/nanoda_lib) (pinned `68d5ca9`) | Independent Lean 4 kernel written in Rust | second kernel in Comparator |
| [lean4export](https://github.com/leanprover/lean4export) | Exports environments for external checkers | used by Comparator |
| [landrun](https://github.com/Zouuup/landrun) | Landlock sandbox | isolates the checked build in Comparator |
| [Palomar registry](https://palomar-registry.org/) ([submission template](https://github.com/PalomarRegistry/PalomarSubmission)) | Challenge/Solution layout and the tool pins used for acceptance | Anthropic projects follow it; our CI reuses its upstream script |
| [CSLib](https://github.com/leanprover/cslib) | Emerging Lean library for computer-science foundations | candidate home for a shared machine model (P8) |
| [uds-psl/cook-levin](https://github.com/uds-psl/cook-levin) (Coq) and the Isabelle AFP [Cook–Levin](https://www.isa-afp.org/entries/Cook_Levin.html) | Mechanized Cook–Levin theorems | reference for P8 encodings |
| Anthropic [`eth/proof/sparsification/`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification) (`SparsificationLemma`, `SparsifyWidthK`, `UniformInK`, …) | Formal sparsification lemma in Lean/Mathlib | candidate source for P9 |
| `openai/math` `ComparatorChallenges/SAT*.lean` | Further SAT statements (computability, sharpness, variance, thresholds) | archived in [`sources/openai-math/lean/ComparatorChallenges`](sources/openai-math/lean/ComparatorChallenges/) for future audits |

## Uncertainties and blocked items

* **Peer review is pending.** A passing kernel check means only that the
  formal statement is proved. The fidelity of the statement (see the audit) and
  the paper's prose claims (e.g. the `E^NP` lower bound) are not covered.
* **P8 is blocked.** Moving the theorems into `Complexity.Machine` needs
  Mathlib (which this repository does not use) or a re-implementation of TM2
  semantics, plus a simulation with polynomial overhead. Until that exists,
  `SubexpKSAT 3` is a named hypothesis here, not a theorem.
* **P9 is not formalized here.** `SETH ⇒ ETH` is therefore not a certified
  result of this repository.
* **P6 rank bound** is checked numerically only for `λ ≤ 4`.
* **`openai-full`** may exceed the time, disk or memory limits of a hosted
  runner. If it does not finish, OpenAI's proof counts as **not
  independently re-verified here**. It is reported as blocked, not as refuted.
* **Secondary sources.** Discovery dates, the review funding and token counts
  come from press coverage of lab statements. OpenAI's own page returned
  HTTP 403.
* **Pinned commits.** All checks refer to `anthropics/formal-math@16a5ce4` and
  `openai/math@4eaee87`. The weekly schedule of the workflow rebuilds the same
  pins. Later upstream changes need a new archive and pin update.

## Reproduce

Local (light):

```sh
lake build proofs.experiments.issue638.lean.ETH
lake env lean experiments/issue638/PrintAxioms.lean
python3 experiments/issue638/check_issue638_status.py
python3 -I experiments/issue638/swap_singlet_ranks.py 4
```

Heavy (CI only): run the workflow *External Lean re-verification (issue 638)*
from the Actions tab (`workflow_dispatch`).
