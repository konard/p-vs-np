# Refutation Plan for Historical Attempts

Status: plan, not a result. Written 2026-11-03. Review quarterly (see
[section F](#f-review-cadence-and-metric)).

This plan orders the work of raising the 116 attempt folders, and the 68
registry-only claims in
[CLAIMED_PROOFS_2017_2026.md](../../literature/CLAIMED_PROOFS_2017_2026.md),
from informal analysis to mechanized evidence. It does not claim that any
attempt is refuted beyond what the
[coverage index](COMMON_ERRORS.md#attempt-coverage-index) records. It makes no
claim about P versus NP.

Every number below comes from a command listed next to it, run on
2026-11-03 against the working tree.

## Contents

- [A. Evidence levels and what "refuted" means](#a-evidence-levels-and-what-refuted-means)
- [B. Triage by error family](#b-triage-by-error-family)
- [C. The first 20 attempts](#c-the-first-20-attempts)
- [D. Intake of the 68 registry-only claims](#d-intake-of-the-68-registry-only-claims)
- [E. Definition of done and checks](#e-definition-of-done-and-checks)
- [F. Review cadence and metric](#f-review-cadence-and-metric)
- [G. Hygiene items found while writing this plan](#g-hygiene-items-found-while-writing-this-plan)

## Starting point

| Quantity | Value | Command |
| --- | --- | --- |
| Attempt folders | 116 | `python3 -I scripts/check_claims.py --count attempt-folders` |
| Claim direction (P = NP / P != NP / unprovable or undecidable) | 63 / 50 / 3 | `python3 -I scripts/check_claims.py --count attempts-p-eq-np` (and `attempts-p-neq-np`, `attempts-other`) |
| Concrete refutation | 2 | `python3 -I scripts/check_claims.py --count coverage-concrete-refutation` |
| Conditional result | 2 | `python3 -I scripts/check_claims.py --count coverage-conditional-result` |
| Identified gap | 1 | `python3 -I scripts/check_claims.py --count coverage-identified-gap` |
| Informal/unverified analysis | 111 | `python3 -I scripts/check_claims.py --count coverage-informal` |
| Folders with a `refutation/` directory | 60 | `ls -d proofs/attempts/*/refutation \| wc -l` |
| Folders with `sorry`, `axiom`, `Parameter` or `Admitted` in some Lean or Rocq file | 115 | see [section G](#g-hygiene-items-found-while-writing-this-plan) |
| Attempt conclusions in `scripts/proof_status.json` | 0 | `grep -c attempts scripts/proof_status.json` |
| Registry-only claims, 2017 to 2026 | 68 | `python3 -I scripts/check_literature_registry.py --type claimed-p-vs-np-proof` |

The two concrete refutations are
[sergey-gubin-2010-peqnp](sergey-gubin-2010-peqnp/) (theorems
`witness_feasible`, `no_hamiltonian_tour`, `paper_correspondence_fails` and
`claimed_soundness_false` in
[GubinPaperCounterexample.lean](sergey-gubin-2010-peqnp/refutation/lean/GubinPaperCounterexample.lean))
and [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/) (theorem
`theorem1_c3_counterexample` in
[ZhuRefutation.lean](guohun-zhu-2007-peqnp/refutation/lean/ZhuRefutation.lean)).
The conditional results are
[anatoly-plotnikov-2007-peqnp](anatoly-plotnikov-2007-peqnp/) and
[matt-groff-2011-peqnp](matt-groff-2011-peqnp/). The identified gap is
[author104-2015-peqnp](author104-2015-peqnp/).

## A. Evidence levels and what "refuted" means

The plan uses the four levels of
[COMMON_ERRORS.md](COMMON_ERRORS.md) with their exact names and meanings:

- **Concrete refutation:** a verified witness falsifies a stated proposition
  under the original input conditions.
- **Conditional result:** a verified result depends on an explicitly stated
  interpretation or additional premise; the paper's full claim remains open.
- **Identified gap:** a specific missing implication or proof obligation has
  been isolated, without a full counterexample to the algorithm.
- **Informal/unverified analysis:** the local notes suggest an error, but this
  index has not audited a source-level proposition and matching witness.

In this repository, "refuted" means **source-level refutation**. That needs
three parts:

1. A faithful formalization, in Lean and in Rocq with identical names, of the
   author's key definition, algorithm or lemma. The README quotes the source
   location (section, equation, page or line) for each transcribed item.
2. A machine-checked proof that this item is false, or that it does not imply
   the author's claim. Usually this is a concrete witness that satisfies the
   source's input conditions and computes the failed result.
3. An assumption report showing only the allowed global assumptions:
   `propext`, `Classical.choice` and `Quot.sound` in Lean, and
   `Classical_Prop.classic` in Rocq.

The following are **not** refutations, and must not be called one:

- a file that does not type-check, or a failed search, timeout or type
  mismatch ([RESEARCH_VISION.md](../../RESEARCH_VISION.md), section 5);
- a theorem about a simplified model, or a theorem that ends in `True`
  ([CONTRIBUTING.md](../../CONTRIBUTING.md), "Code Quality");
- a proof that uses `sorry`, `admit`, `Admitted`, `axiom`, `Parameter` or
  `native_decide`;
- a status line such as "Refuted" in an attempt README, or the presence of a
  `refutation/` folder. Both are informal until the index row says
  "Concrete refutation";
- a published critique that has not been mechanized. It is a strong reason to
  prioritize an attempt (section C). The index level stays informal until the
  critique's witness is checked here.

When a faithful transcription needs an interpretation choice (an ambiguous
step, an unstated tie-break, an unspecified LP solver), the honest level is
**Conditional result**, with the choice named in the README. When only a
missing implication can be stated precisely, the level is **Identified gap**.

Result classes for pull requests follow
[CONTRIBUTING.md](../../CONTRIBUTING.md): most items here are
"algorithm-specific refutation", "restricted-model lower bound" or "known
theorem mechanized". None is a "conditional general result" or an
"unconditional general result" about P versus NP.

## B. Triage by error family

Family numbers are those of [COMMON_ERRORS.md](COMMON_ERRORS.md). Do not
renumber them.

- **Primary** is the number of index rows whose `Family` column names the
  family. These sum to 116.
- **Listed** is the number of folders in the family's "Similar works" list. A
  folder can be listed in several families.

Commands:

```sh
# primary family per index row
awk -F'|' '/^\| \[/{gsub(/ /,"",$3); n[$3]++} END{for(k in n) print k, n[k]}' \
  proofs/attempts/COMMON_ERRORS.md | sort -n
# folders listed under each family
awk '/^### [0-9]+\./{f=$2; sub(/\./,"",f)} /^## Attempt Coverage Index/{exit} \
  /^- \[/{n[f]++} END{for(k in n) print k, n[k]}' \
  proofs/attempts/COMMON_ERRORS.md | sort -n
```

Size scale. **S**: the template and the shared code exist; the work is one
transcription and one witness. **M**: one new shared module is needed first
(for example a graph library), then each attempt is S. **L**: the faithful
statement needs a new model or a deep known theorem that is not mechanized
here; most attempts will stop at Identified gap.

Reusable code referred to below:

- shared model: [Complexity.lean](../complexity/lean/Complexity.lean)
  (`Machine`, `InP`, `InNP`, `PEqualsNP`) and
  [Machines.lean](../experiments/issue532/lean/Machines.lean) (`CNF`,
  `Satisfiable`, `encodeCNF`, `SAT`, `PolyReduces`, `NPHard`, `diag_not_inP`);
- verified DPLL: [NPSubsetP.lean](../experiments/issue8/lean/NPSubsetP.lean)
  (`dpll_correct`, `dpllSAT_eq_SAT`, `dpllSAT_calls_le`,
  `calls_bound_not_polynomial`);
- 2-SAT and local-consistency harness:
  [experiments/issue587](../../experiments/issue587/README.md)
  (`kardash_2sat.py`, `Audit.lean`, `check.sh`);
- exact LP witness pattern:
  [experiments/issue578](../../experiments/issue578/README.md)
  (`check_paper_lp.py`) and the Gubin 2010 files above;
- residual-key counterexample pattern:
  [ResidualKey.lean](../experiments/issue567/lean/ResidualKey.lean)
  (`coarseKey_not_satisfiability_complete`, `family_encoded_lengths`);
- LP rounding schema: [Idea36.lean](../experiments/issue532/lean/Idea36.lean)
  (`FracCover`, `round`, `no_exact_rounding`, `ExactRoundingObligation`);
- decision trees and relativization:
  [Idea02.lean](../experiments/issue532/lean/Idea02.lean) (`DecidesSearch`),
  [Idea38.lean](../experiments/issue532/lean/Idea38.lean)
  (`no_shallow_tree_decides_or`, `relativizing_cannot_prove`,
  `machineRelativizing_cannot_settle`, which takes `BGSCollapse` and
  `BGSTestSeparation` as named premises);
- local search: [Idea06.lean](../experiments/issue532/lean/Idea06.lean)
  (`exact_local_search_decides`, `localMin_decides`);
- circuits: [Circuits.lean](../experiments/issue532/lean/Circuits.lean)
  (`CircuitDecides`, `InPPoly`, `superpoly_iff_not_inPPoly`,
  `pNotEqualsNP_of_superpoly`, which takes `PSubsetPPoly` as a premise).

| # | Family | Primary | Listed | Generic refutation template | Missing shared infrastructure | Size |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Lower bound assumed | 8 | 13 | State the author's argument as a lower bound for a named algorithm class. Prove the class bound (restricted-model lower bound) and exhibit a polynomial algorithm outside the class, so the step "class bound implies all algorithms" fails. Decision-tree lemmas in Idea02 and Idea38. | An "algorithm class" interface as a predicate on `Machine` | M |
| 2 | Hidden exponential work | 5 | 13 | Write the algorithm as a cost-instrumented function. Prove a run-time lower bound on an explicit family, as `dpllSAT_calls_le` and `calls_bound_not_polynomial` do for DPLL. | Generic step-counter wrapper | S to M |
| 3 | LP/SDP relaxation | 10 | 11 | Transcribe the paper's constraints exactly. Find a fractional feasible or optimal point with exact rationals in Python, then check it in Lean and Rocq by `decide` on a graph or formula without the property (Gubin 2010 pattern). For rounding claims use the Idea36 schema. | Shared rational LP feasibility checker; digraph type with a decidable Hamiltonian-cycle test. Yannakakis (1991) and Fiorini et al. are not in the registry and not mechanized | M |
| 4 | Invalid reduction | 8 | 11 | Write the transformation as a function on `CNF` or graphs. Exhibit one input where membership is not preserved, checked by brute force (`dpllSAT`, issue587 SCC test). | Graph types for clique and matching | S |
| 5 | Easier or different problem | 9 | 11 | Run the author's algorithm on a small general instance. Compare with brute force (maximum clique, Hamiltonian cycle, optimal tour) and prove the outputs differ. | Graph library over `Fin n`: adjacency, clique, Hamiltonian cycle, tour cost, brute-force deciders | M |
| 6 | Local vs global consistency | 6 | 8 | Use the issue587 witnesses (arc-consistent unsatisfiable triangle, unit-propagation fixpoint) or a small search to find an unsatisfiable formula that the author's consistency test accepts. | 3-SAT version of the issue587 pair-cleaning harness | S |
| 7 | Counting or compression | 3 | 7 | Exhibit a finite witness that breaks the counting bound (Zhu pattern), or two inputs that collide on all data the algorithm keeps (Groff and ResidualKey patterns). | None beyond core Lean | S |
| 8 | Heuristics or experiments as proof | 6 | 9 | Name the unproved universal step as a hypothesis (Identified gap). For a stated heuristic, search adversarial instances with a Python harness and check any witness in Lean and Rocq. | Shared adversarial-instance harness | M |
| 9 | Nondeterminism, randomness, physics | 5 | 7 | Show the author's model is not `Machine`, or that it charges exponential resources. Usually ends at Identified gap. | `ModelEquivalence` is listed in [HYPOTHESES.md](../HYPOTHESES.md) but not defined | L |
| 10 | Provability vs complexity | 11 | 12 | Mechanize the known theorem that every `InNP` language is decided by some (exponential-time) `Machine`, then locate the step that needs an undecidable member of NP. Independence claims need a proof-system model. | Lemma "NP languages are machine-decidable" in the shared model; no proof-system model | M (decidability) to L (independence) |
| 11 | Nonstandard definitions | 6 | 8 | Formalize the author's class and prove it differs from `Complexity.InNP` or `InP` on one concrete language. | None for precise definitions | S to M |
| 12 | Circular premise | 5 | 13 | Keep the premise as an explicit argument (Conditional result). Prove that the premise implies, or is equivalent to, the conclusion. Then search small cases for a counterexample to the premise. | None | S |
| 13 | Diagonalization or independence | 3 | 8 | If the construction relativizes, apply `machineRelativizing_cannot_settle` (conditional on `BGSCollapse`, `BGSTestSeparation`). For a diagonal step, compare with `diag_not_inP`. | Oracle versions of the author's constructions | L |
| 14 | Barrier-limited technique | 1 | 12 | Relativization template as in family 13. For "proves too much" arguments, show the claimed property also holds for a problem in P. | Natural proofs and algebrization are registered but not mechanized; XOR-SAT in P is not mechanized | L |
| 15 | Verification vs search | 3 | 7 | Show the argument applies equally to a problem in P, or mechanize the search-to-decision self-reduction for SAT in the shared model. | Search-to-decision lemma for SAT | M |
| 16 | Uniformity and circuits | 2 | 5 | Show the claimed bound is for a restricted circuit class, or that it needs `PSubsetPPoly` plus a superpolynomial bound that is not proved (Circuits.lean). | Monotone or bounded-depth circuit model | M to L |
| 17 | Encoding size | 6 | 7 | Compute the author's representation size on an explicit family with `encodeCNF` (ResidualKey `family_encoded_lengths` pattern), and show it is exponential in the input length. | None | S |
| 18 | False statements | 4 | 5 | Mechanize a counterexample to the false intermediate lemma. If the lemma is only "not known", it is not false: record an Identified gap. | Depends on the lemma | M |
| 19 | Incomplete or withdrawn | 10 | 15 | No template. Keep at Informal/unverified analysis until a full text is accessible. Record the author's withdrawal note verbatim. | None | not scheduled |
| 20 | Structure theorem from one class | 5 | 5 | Same as family 1: prove the class-restricted bound as a restricted-model lower bound, then show one algorithm outside the class. | Same as family 1 | M |

Order of infrastructure work, by how many primary rows each unblocks:

1. Graph library over `Fin n` with brute-force deciders (families 3, 4, 5;
   27 primary rows). Lean and Rocq, no Mathlib, `decide`-friendly.
2. Shared exact-rational LP feasibility checker, generalized from
   `experiments/issue578/check_paper_lp.py` (family 3; 10 primary rows).
3. 3-SAT local-consistency harness, generalized from issue587 (family 6 and
   several family 4 rows).
4. "NP languages are machine-decidable" in the shared model (family 10; 11
   primary rows).
5. Algorithm-class interface and a decision-tree bridge (families 1 and 20;
   13 primary rows).

Each new shared module follows [CLAUDE.md](../../CLAUDE.md): paired Lean and
Rocq files with identical names, no escape hatches, and Rocq files added to
`_CoqProject` in dependency order.

## C. The first 20 attempts

Ranking rules, in order:

1. a precise algorithm or a precise false lemma exists in an accessible text;
2. a published critique supplies a witness to check;
3. existing code is reused;
4. one infrastructure module unblocks several attempts;
5. rows already at Conditional result or Identified gap come before new rows
   of the same cost.

Folders 19 and 20 are restricted-model items, so that both claim directions
are covered.

| Rank | Folder | Year | Claim | Family | Lemma or definition to formalize | Expected result class | Reusable code | Why early |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/) | 2011 | P = NP | 6 | Pair cleaning (Definitions 3 to 15) on 3-CNF: find an unsatisfiable 3-CNF whose cleaned tables stay nonempty, which contradicts the claimed decision procedure | algorithm-specific refutation | `experiments/issue587/kardash_2sat.py`, `Audit.lean`, `check.sh` | Pair cleaning is already implemented for 2-CNF; source copy is local |
| 2 | [lizhi-du-2010-peqnp](lizhi-du-2010-peqnp/) | 2010 | P = NP | 6 | Algorithm 1, Step 3 (intersection of useful units) on the smallest member of the satisfiable family in the critique arXiv:2404.04395; prove the formula is satisfiable and that the algorithm rejects it | algorithm-specific refutation | `dpllSAT`, issue587 harness | Published witness family; precise step |
| 3 | [anatoly-panyukov-2014-peqnp](anatoly-panyukov-2014-peqnp/) | 2014 | P = NP | 3 | Theorem 1 ("the set of optimal solutions of the relaxed problem (10) contains an integer solution"): exhibit a graph where a fractional point beats every integer point of LP (10) | algorithm-specific refutation | Gubin 2010 LP pattern, `check_paper_lp.py` | Single precise false lemma; paper and notes in `experiments/panyukov-analysis/` |
| 4 | [michael-laplante-2015-peqnp](michael-laplante-2015-peqnp/) | 2015 | P = NP | 5 | The 3-clique merging procedure on the counterexample graph of Cardenas et al., arXiv:1504.06890; prove the output is smaller than the maximum clique | algorithm-specific refutation | graph library (to build) | Published counterexample; builds the graph library |
| 5 | [dhami-2014-peqnp](dhami-2014-peqnp/) | 2014 | P = NP | 4 | The Tamta-Pande-Dhami clique algorithm on the same critique's counterexample | algorithm-specific refutation | graph library, rank 4 files | Same critique as rank 4; low marginal cost |
| 6 | [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/) | 2006 | P = NP | 4 | The SAT-to-2-SAT transformation: one CNF whose satisfiability differs from that of its image | algorithm-specific refutation | `dpllSAT`, issue587 SCC test | Precise transformation; critique arXiv:0804.2699 cited in the folder |
| 7 | [antano-maknickas-2011-peqnp](antano-maknickas-2011-peqnp/) | 2011 | P = NP | 3 | LP relaxation plus recovery g(X) = floor(X) mod 2 (arXiv:1203.6020): an optimal LP point whose recovered assignment falsifies a satisfiable 3-CNF | algorithm-specific refutation, or Conditional result if the LP optimum is not unique | Idea36 rounding schema, LP checker | Source copy is local; precise recovery map |
| 8 | [charles-sauerbier-2002-peqnp](charles-sauerbier-2002-peqnp/) | 2002 | P = NP | 6 | The C/DNF reduction operator (cs/0205064): an unsatisfiable CNF on which it terminates without deriving the empty set | algorithm-specific refutation | issue587 arc-consistency witnesses | Local-consistency witnesses already exist |
| 9 | [louis-coder-2012-peqnp](louis-coder-2012-peqnp/) | 2012 | P = NP | 6 | Algorithm E-1.0 (the `Active[]` elimination loop): an unsatisfiable 3-CNF for which some `Active` entry stays true | algorithm-specific refutation | issue587 harness | Precise loop; paper copy at `experiments/louis-coder-2012.pdf` |
| 10 | [howard-kleiman-2006-peqnp](howard-kleiman-2006-peqnp/) | 2006 | P = NP | 5 | The modified Floyd-Warshall procedure on M(s): an asymmetric instance where the returned tour costs more than the optimum | algorithm-specific refutation | graph library, brute-force tour search | Source copy is local |
| 11 | [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/) | 2006 | P = NP | 6 | The vertex-selection rules of the Hamiltonian-cycle algorithm: a Hamiltonian graph where the algorithm reports no cycle | algorithm-specific refutation | graph library | Source copy is local |
| 12 | [qi-duan-2012-peqnp](qi-duan-2012-peqnp/) | 2012 | P = NP | 6 | The growth-process insertion step (arXiv:1208.0542): an instance where optimal insertion of one vertex does not extend an optimal tour | algorithm-specific refutation | graph library | Precise greedy step |
| 13 | [vladimir-romanov-2010-peqnp](vladimir-romanov-2010-peqnp/) | 2010 | P = NP | 17 | Compact triplet structures and their consistency procedure (arXiv:1011.3944): an unsatisfiable 3-CNF accepted, or an explicit family with exponential structure size | algorithm-specific refutation | issue587 harness, `encodeCNF` | Source copy is local |
| 14 | [moustapha-diaby-2004-peqnp](moustapha-diaby-2004-peqnp/) | 2004 | P = NP | 3 | The TSP polytope formulation: a feasible extreme point with no corresponding tour | algorithm-specific refutation | LP checker, Gubin 2010 pattern | Same template as rank 3; the model is large, so the smallest witness may be costly |
| 15 | [anatoly-plotnikov-2007-peqnp](anatoly-plotnikov-2007-peqnp/) | 2007 | P = NP | 12 | Conjecture 1 as stated: search small graphs for a counterexample, or prove it for small orders | raise Conditional result to algorithm-specific refutation; otherwise keep Conditional result | existing attempt files | Already conditional |
| 16 | [matt-groff-2011-peqnp](matt-groff-2011-peqnp/) | 2011 | P = NP | 7 | The full reconstruction step: two 3-CNFs with different satisfiability that agree on every value the algorithm reads | raise Conditional result to algorithm-specific refutation | ResidualKey pattern, existing collision | Already conditional |
| 17 | [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/) | 2007 | P = NP | 7 | Lemma 4 (code-class bound) as stated in the paper, beyond `lemma4_code_bound_counterexample` | extend the Concrete refutation to Lemma 4 | `ZhuRefutation.lean`, `experiments/issue580/projector_witness.py` | Only open part of an existing refutation |
| 18 | [frank-vega-delgado-2010-pneqnp](frank-vega-delgado-2010-pneqnp/) | 2010 | P != NP | 10 | Known theorem: every `InNP` language is decided by some `Machine`. Then state the missing implication "CERTIFYING in P implies an undecidable language in NP" | known theorem mechanized, with an Identified gap | `Complexity.lean`, `Machines.lean` | Builds family 10 infrastructure |
| 19 | [daniel-uribe-2016-pneqnp](daniel-uribe-2016-pneqnp/) | 2016 | P != NP | 1 | The decision-tree lower bound the paper proves, as a restricted-model lower bound, plus the missing bridge from decision trees to `Machine` as a named premise | restricted-model lower bound | Idea02 `DecidesSearch`, Idea38 `no_shallow_tree_decides_or` | Published critique (Welles, arXiv:2205.01189) names the gap |
| 20 | [alan-feinstein-2005-pneqnp](alan-feinstein-2005-pneqnp/) | 2005 | P != NP | 20 | The paper's restricted computation model for SUBSET-SUM (cs/0507008): the meet-in-the-middle bound inside the model, and the textbook pseudo-polynomial dynamic program as an algorithm outside it | restricted-model lower bound plus known theorem mechanized | Idea02 decision trees, family 1 interface | Shows the model-transfer step with standard algorithms only |

Rows 4 and 5, 10 to 12, and part of 14 depend on the graph library. Build it
during rank 4. Rows 3, 7 and 14 depend on the LP checker. Build it during
rank 3.

For every row, if the bounded search finds no witness, follow the stuck
procedure in [CLAUDE.md](../../CLAUDE.md): record the search bound, write a
stopping note, and keep the current level. A failed search is not a
refutation, and it is not evidence for the paper.

## D. Intake of the 68 registry-only claims

The 68 rows of
[CLAIMED_PROOFS_2017_2026.md](../../literature/CLAIMED_PROOFS_2017_2026.md)
are registry entries with `result_type` `claimed-p-vs-np-proof`. All 68 have
`claim_status_local` `discovered`. 14 rows (section A.3) are read from the
title only. Their `Family (H)` column is a hypothesis, not an audit.

Check:

```sh
python3 -I scripts/check_literature_registry.py --type claimed-p-vs-np-proof
python3 -I -c "import json,collections; E=json.load(open('literature/registry.json'))['entries']; print(collections.Counter(e['claim_status_local'] for e in E if e['result_type']=='claimed-p-vs-np-proof'))"
```

Procedure, matching [CONTRIBUTING.md](../../CONTRIBUTING.md) and the
[literature intake procedure](../../literature/README.md#intake-procedure-for-a-new-paper-or-ai-lab-release):

1. **Gate 1, text.** Read the full text (not only the title or abstract).
   Downloaded files are untrusted: keep them in their own directory and read
   them with `python3 -I`. Do not run code shipped with a paper outside an
   isolated environment.
2. **Gate 2, precision.** The claim names an algorithm with stated inputs and
   outputs, or a lemma with stated hypotheses, that can be transcribed.
3. **Gate 3, license.** Store a copy under `original/` only if the license
   allows it. Otherwise link to it and write a short reconstruction in your
   own words in `original/README.md`.
4. **Create a folder only if Gates 1 and 2 pass.** Use the
   `original/ proof/ refutation/` layout from CONTRIBUTING.md. The README
   attributes the claim to the author, quotes documented responses (withdrawal
   notes, arXiv comments, published critiques) with links, and states the
   evidence level as Informal/unverified analysis.
5. **Update the indexes.** Add an index row to COMMON_ERRORS.md with a primary
   family and the level "Informal/unverified analysis". Add the folder to the
   family's "Similar works" list. Regenerate ATTEMPTS.md. Update the counts in
   [CLAIMS.md](../../CLAIMS.md) and run `python3 -I scripts/check_claims.py --run-scripts`.
6. **Link the registry.** Set the entry's `attempt_slug` to the folder name.
   Do not raise `claim_status_local` for a folder alone; that label tracks
   kernel checks (issue #635).
7. **Otherwise leave the row in the registry.** Keep `claim_status_local`
   `discovered`. Record the decision (`defer` or `reject`) and its reason in
   the row's status cell, for example "defer: title only" or "defer: no
   precise algorithm in v3".

Intake order:

1. Rows with a published critique that contains a witness: 27 (Chen 2023,
   counterexamples in arXiv:2404.00006), 68 (Czerwinski 2021, counterexample
   in arXiv:2304.14575), 28 (Quigley 2024, arXiv:2510.22985), 17 (Kumar 2021,
   exponential runs in arXiv:2112.06062), 29 (Deng 2024, arXiv:2507.09018).
2. Other rows with a published critique: 1 (Blum 2017), 3 (Cho 2018), 9 (Sima
   2019), 11 (Gordeev 2020), 24 (Xu and Zhou 2023), 30 (Lin 2024).
3. Rows that claim Lean code: 37 (Arthanari 2025 to 2026) and 35 (Tang 2025;
   commenters report that the linked repository returns 404). For these, the first deliverable is an axiom
   inventory with `#print axioms` on the author's declarations, run in an
   isolated environment, with the result recorded in the registry. A clean
   inventory does not validate the claim: the bridge from the author's model
   to `Complexity.InP` still has to be named.
4. Remaining arXiv, HAL and journal rows, oldest first.
5. Title-only rows (section A.3) stay in the registry until a full text is
   read.

Critiques used in sections C and D should themselves be added to
`literature/registry.json` as `critique` entries before the work starts.
As of 2026-11-03 the registry holds 4 critique entries
(`python3 -I scripts/check_literature_registry.py --type critique`). The
critiques arXiv:1504.06890, arXiv:2404.04395, arXiv:2205.01189 and
arXiv:0804.2699 are cited in attempt READMEs but are not registry entries.

## E. Definition of done and checks

### Concrete refutation

An attempt moves to "Concrete refutation" only when all of these hold:

1. `refutation/README.md` quotes the exact source proposition, with its input
   conditions and source location, and explains the witness.
2. `refutation/lean/<Name>.lean` and `refutation/rocq/<Name>.v` transcribe the
   source definitions, with identical theorem names. The Rocq file is listed
   in `_CoqProject` in dependency order.
3. The main theorem states the negation of the source proposition (for
   example `claimed_soundness_false : ¬ PaperClaim`). It does not end in
   `True`, and it does not quantify over arbitrary objects unrelated to the
   paper's construction.
4. The witness satisfies the source's input conditions, and the proof
   computes the failure with the kernel (`decide` or `decide +kernel` in Lean,
   ordinary reduction in Rocq). No `native_decide`.
5. `#print axioms` and `Print Assumptions` on the main theorem show only the
   allowed assumptions. The output is pasted in the README and in the PR.
6. Any search script lives in `experiments/issueN/`, uses exact arithmetic,
   runs with `python3 -I`, and has a unit test.
7. Mutation tests reject at least: the witness with one constraint, edge or
   clause changed; the theorem with the source condition removed; and an index
   row that says "Concrete refutation" for a folder without refutation files.
8. The index row, the folder README status line, ATTEMPTS.md and the counts
   in CLAIMS.md change in the same PR.
9. The PR uses the template in [CLAUDE.md](../../CLAUDE.md), with result class
   "algorithm-specific refutation" (or "restricted-model lower bound") and
   provenance "known theorem newly mechanized" when a published critique
   supplied the witness, otherwise "new-to-repository engineering". It uses
   "Refs #N" unless it delivers the whole issue.

Adding the main theorem to `scripts/proof_status.json` is a separate,
reviewed step. Until then the refutation is mechanized but not certified, in
the sense of [CLAUDE.md](../../CLAUDE.md) rule 10.

### Conditional result and Identified gap

- **Conditional result:** items 1 to 9 above, except that the theorem takes
  the interpretation choice or extra premise as an explicit argument, defined
  once as a `Prop`. If the premise is a property of the paper (not a
  complexity-theoretic hypothesis), it stays in the attempt folder. Premises
  about complexity classes go into [HYPOTHESES.md](../HYPOTHESES.md).
- **Identified gap:** the missing implication is a named `Prop` in Lean and
  Rocq, the README says which source step needs it, and no theorem claims it
  is false.

### Checks to run before a PR

```sh
python3 scripts/check_attempt_structure.py --path proofs/attempts/<folder>/
lake build <module.name>
rocq compile -Q . '' proofs/attempts/<folder>/refutation/rocq/<Name>.v
python3 scripts/check_proof_status.py
python3 -I scripts/check_claims.py --run-scripts
python3 -m unittest discover -s experiments/issue580 -p 'test_*.py'
python3 -m unittest discover -s experiments/issueN -p 'test_*.py'
```

The issue580 test checks that every folder has exactly one index row with
exactly one evidence label. Mutation test 7c above is proposed; no script
enforces it yet.

### Vocabulary rule

Informal analysis must never be called a refutation. In READMEs, index rows,
PR titles and commit messages, the words "refuted" and "refutation" are
reserved for rows at "Concrete refutation". Use "suspected error",
"identified gap" or "conditional result" otherwise. A folder named
`refutation/` is a location, not a verdict.

## F. Review cadence and metric

Review in the first week of February, May, August and November. The next
review is due in February 2027. Each review records, with the commands below:

1. counts per evidence level (the headline metric);
2. counts per primary family, and per family at each level;
3. attempt conclusions in `scripts/proof_status.json`;
4. registry-only claims by intake decision;
5. progress on the top-20 list, with stopping notes for stalled items.

```sh
python3 -I scripts/check_claims.py --run-scripts
grep "^| \[" proofs/attempts/COMMON_ERRORS.md | grep -o "| [A-Za-z/ ]* |$" | sort | uniq -c
awk -F'|' '/^\| \[/{gsub(/^ +| +$/,"",$3); gsub(/^ +| +$/,"",$5); n[$3" "$5]++} \
  END{for(k in n) print k": "n[k]}' proofs/attempts/COMMON_ERRORS.md | sort -n
grep -c attempts scripts/proof_status.json
python3 -I scripts/check_literature_registry.py --type claimed-p-vs-np-proof --json
```

Baseline on 2026-11-03: 2 Concrete refutation, 2 Conditional result, 1
Identified gap, 111 Informal/unverified analysis; 0 attempt conclusions
certified; 68 registry-only claims, all `discovered`.

A review that finds the counts unchanged says so. It does not restate the
plan as progress.

## G. Hygiene items found while writing this plan

These are outside the files this plan may change. They are listed so that a
follow-up PR can fix them.

1. **Status lines.** 57 attempt READMEs contain a status line with "refuted"
   (`grep -l -i -E "status.{0,20}refuted" proofs/attempts/*/README.md | wc -l`),
   while the index has 2 concrete refutations. Rewrite these lines to name
   the evidence level.
2. **Isabelle mentions.** 62 attempt READMEs mention Isabelle
   (`grep -l -i isabelle proofs/attempts/*/README.md | wc -l`). Isabelle is
   archived in `archive/isabelle/` and not checked.
3. **Escape hatches.** 115 of 116 folders have `sorry`, `axiom`, `Parameter`
   or `Admitted` in at least one Lean or Rocq file. The exception is
   sergey-gubin-2010-peqnp. This is allowed in `proofs/attempts/` but means
   none of those files is a refutation as it stands. Command:
   `grep -rl --include='*.lean' --include='*.v' -E "^\s*(axiom|Axiom|Parameter|Admitted|sorry)|\bsorry\b|Admitted\." proofs/attempts | sed 's|proofs/attempts/\([^/]*\)/.*|\1|' | sort -u`
   (this also lists a stray top-level file, `proofs/attempts/MeyerAttempt.lean`).
4. **has-also-2001-pneqnp.** Done on 2026-11-03. The folder README now says
   that EXP ⊆ NP is equivalent to NP = EXP, an open question, and the Lean
   and Rocq headers carry a correction note. The axioms in those files still
   assume an open problem; replacing them is part of family 19 work.
5. **ATTEMPTS.md generator.** Done on 2026-11-03. The legend for `?` and the
   notes on claim symbols and evidence levels are emitted by
   `generate_markdown_list` in `scripts/check_attempt_structure.py`, and
   regeneration reproduces ATTEMPTS.md exactly.
