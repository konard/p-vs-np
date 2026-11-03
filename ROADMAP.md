# Roadmap

This is the repository's operative plan. It gives order and dependencies, not
dates. No date is promised for any mathematical result. The method behind the
plan is in [RESEARCH_VISION.md](RESEARCH_VISION.md).

[DETAILED_SOLUTION_PLAN.md](DETAILED_SOLUTION_PLAN.md) and
[SOLUTION_STRATEGIES.md](SOLUTION_STRATEGIES.md) are background reading for
individuals who want to learn the field. They describe a generic multi-year
study plan. They are not the plan of this repository. Where they disagree
with this file, this file applies.

Update this file when a milestone changes state, and keep the date below
current.

## Status at 2026-11-03

`main` is at `ecedd2b`. "PR" means an open pull request that has not been
merged.

| Milestone | Issue / PR | State |
| --- | --- | --- |
| Shared model, P ⊆ NP (`Complexity.pSubsetNP`) | #571 | Done, certified |
| SAT ∈ NP (`SATVerifier.satInNP`) | #532 | Done, certified |
| Clocked SAT: Π⁰₂ form implies P ≠ NP with no premise | #7 | Done, certified |
| DPLL correctness and `2^(|w|+1)` call bound | #8 | Done, certified; no machine, no `Run` cost |
| 41 idea dossiers over the shared model | #532 | Done; verdicts in the research log |
| Bounded tableau semantics (Milestone A, first slice) | #568, PR #622 | Merged |
| Circuit decoder; residual-key counterexample (N1 slice, N3) | #567, PR #623 | Merged |
| `CircuitSATInNP` (N1) | #625, PR #631 | Proved in PR; CI green; reviewed; waiting to merge |
| `PSubsetPPoly` (N2) | #626, PR #632 | Proved in PR; CI green; reviewed; waiting to merge |
| `SATHard`, Cook-Levin (Milestone A) | #624, PR #630 | Slices 1-2 of 4 in PR; reduction machine and `satHard` missing; CI red |
| ETH/SETH definitions; ETH ⇒ P ≠ NP, SETH ⇒ P ≠ NP | #638, PR #639 | Proved in PR; overclaims and "Fixes #638" to correct |
| Canonical formal statement (FORMAL_STATEMENT.md) | #628 | Written in the working tree; checked by `scripts/check_formal_statement.py`; not yet pushed |
| Hypothesis manifest (proofs/HYPOTHESES.md) and CI check | #629 | Written in the working tree; CI step added to `verification.yml`; not yet pushed |
| Claims ledger (CLAIMS.md) and `scripts/check_claims.py` | issue to be opened | Written in the working tree; CI step added; not yet pushed |
| Literature registry (`literature/`) | #634, #637 | 162 entries in the working tree; validated and rendered in CI; not yet pushed |
| Bounded retrieval, validation record, prior-art workflow | #633, #635, #636 | Open; workflow text added to CONTRIBUTING.md |
| Retire legacy toy P/NP frameworks | #627 | Open |
| Milestone B: charged DPLL machine | #568 | Not started |
| Milestone C: residual sharing | #568 | Not started |
| N3: `ResDerives` extraction from Davis-Putnam (Idea 27) | #567 | Not started |
| Williams ingredients | #567, #629 | Open premises |
| `Complexity.PEqualsNP` or `Complexity.PNotEqualsNP` | #568, #567 | Open |

## Now (next PRs)

1. **Merge #631, then #632.** Resolve the one textual conflict in
   `proofs/experiments/issue10/README.md` by keeping #631's wording, and drop
   `PSubsetPPoly` from that file's list of explicit hypotheses. Apply the
   reviewed text fixes first or as a follow-up:
   - stale "conditional on `CircuitSATInNP`" lines in
     `proofs/experiments/p_not_equal_np_proof_attempt.md` and
     `proofs/experiments/README.md`;
   - stale "not mechanised" lines for `PSubsetPPoly` in the research log,
     `experiments/issue532/MACHINE_REFACTOR_GUIDE.md:38` and
     `rocq/Idea31.v:447` (#632 review, item 2);
   - register the verifier theorems of #631 in `scripts/proof_status.json`,
     and register `fastCircuitSAT_of_inP_sat` there too, since the #630 gate
     depends on its post-#631 type (#631 review, items 3 and 6);
   - rename `ppoly_strictly_bigger_than_p_if`, which is now unconditional
     (#632 review, item 3);
   - move the `NandCompiler` wire lemmas into `CircuitModel` so that #630 can
     delete its copies (#632 review, item 4).

   The review comments on #631 and #632 (2026-11-03) are the full list.
2. **Rebase #630 on the result.** As of 2026-11-03 it is marked ready for
   review while CI is red; convert it to draft until CI is green (hard rule 7).
   - Fix the failing proof at `Compiler.lean:138-139`.
   - Make `CookLevin.lean` import `Schema`, not `Compiler`, so the finished
     slices do not depend on the broken module.
   - Delete the unused `CircuitCNF` and `ConstantEmitter` modules. They cause
     about half of the conflicts with #631 and #632 (the `Idea41` and
     `Circuits` edits: 4 of the 8 conflicting files in a trial
     `git merge-tree` on 2026-11-03). The rest are in `verification.yml`,
     its test and `scripts/proof_status.json`.
   - Update the completion gate to the post-#631 signature
     `InP SAT → FastCircuitSAT`.
   - Reuse `Issue626.Window` instead of adding a second window layer.
3. **Correct #639 before merging.** Use "Refs #638". Restate P3 as "not
   derivable from the bound alone". Say "at least as strong as P ≠ NP;
   strictness unknown". Describe the identity as the upstream README's hint,
   not the paper's identity. Drop "exact over ℚ" for the modular rank check.
   Update the `openai-full` status: in the last finished run the build passed
   but Comparator did not accept the proof. Make heavy jobs manual-dispatch
   only.
4. **Land the definition documents.** FORMAL_STATEMENT.md (#628),
   proofs/HYPOTHESES.md with `scripts/check_formal_statement.py` (#629), and
   the literature registry with `scripts/check_literature_registry.py` (#634),
   and the claims ledger CLAIMS.md with
   `python3 scripts/check_claims.py --run-scripts`.
   The links from README.md are already added in the working tree.

## Next

Items can run in parallel unless a dependency is stated.

- **Review follow-ups (#641).** Close the gaps the 2026-11-03 review found:
  weak checks in `scripts/check_claims.py`, 15 claims missing from
  CLAIMS.md, duplicate `NTimeHierarchy` and `InNTIME` definitions, and
  registry entries for the critiques the refutation plan relies on.
- **#624 slices 3-4.** Build the reduction as a `Complexity.Machine` with a
  polynomial `Run` bound, then assemble `satHard` and `cookLevin`. Make the
  18 bridges unconditional, keeping primed conditional names. Then re-derive
  the dossier theorems that take `SATHard` as unconditional corollaries where
  `SATHard` is all they need, and keep the premise elsewhere. Update the
  Idea 12 and Idea 29 dossiers accordingly: their theorems
  (`Idea12.lean:430`, `Idea29.lean:489,493`) are not in the #630 gate, so
  their "under the named hypothesis `SATHard`" wording stays true until those
  theorems are re-derived (#630 review, item 6). Depends on: Now item 2.
- **#627.** Archive or rebuild `proofs/p_eq_np/` and
  `proofs/experiments/{lean,rocq}/PvsNPProofAttempt.*`. Add the CI check that
  no axiom or admission exists outside `proofs/attempts/`.
  Also retire `experiments/issue573/AuditBefore.*` and
  `experiments/issue574/PolynomialRegression.*`, which import those files.
- **`_CoqProject` order.** `experiments/issue567/{Assumptions,DecoderRegression}.v`,
  `experiments/issue568/TraceRegression.v` and the issue574 files are listed
  before the modules they import (hard rule 2 asks for dependency order;
  `coqdep` hides the problem). Reorder them. Small.
- **Unpaired theorem.** `Idea18.unit_size_reduction_exists` has no Rocq twin
  (see Known defects in proofs/HYPOTHESES.md). Add the twin or move the Lean
  theorem out of the paired file. Small.
- **#629 CI enforcement.** CI fails on an unregistered hypothesis or on a
  registered one that is discharged but still used as an argument. Rename one
  of the two `NTimeHierarchy` definitions (Idea 16 and Idea 41). Require a
  `## Result class` and `## Explicit hypotheses` section in each
  `proofs/experiments/issueN/README.md`.
- **Checkable closing rule (#629, or an issue to be opened).** Add an
  optional `type` field to the entries of `scripts/proof_status.json` and make
  `scripts/check_proof_status.py --lean/--rocq` verify that the declaration
  has exactly that type. The closing theorems of #567 and #568 then carry
  `Complexity.PNotEqualsNP` or `Complexity.PEqualsNP`, and "no arguments" is
  checked by CI instead of by reading the PR.
- **#633-#637 reuse workflow.** Bounded retrieval with a disk budget that
  refuses full clones by default (#633). Validation records (#635). The
  two-source pilot on openai/math family 102 and a Cook-Levin formalization
  (#636).
- **Milestone B (#568).** A `Complexity.Machine` that implements a specified
  DPLL variant, with all-input correctness and an honest worst-case `Run`
  bound, even if exponential. Keep the #610 rollback counterexample.
- **N3 (#567).** Extract a `ResDerives` certificate from a full Davis-Putnam
  elimination run (Idea 27, reusing Idea 28). Relate its size to the charged
  work. State exactly which extensions (clause learning, extension variables)
  escape it.
- **`NPClosedUnderReductions` (Idea 23, #629).** A bridge row: compose a
  reduction machine with a verifier. It uses no P-membership fact, so it is
  independent of the next item and may proceed in parallel with it.
  proofs/HYPOTHESES.md lists it at step 2 of its discharge order.
- **Small P-membership premises (#629).** The eight `P-membership` rows of
  proofs/HYPOTHESES.md. Each is an explicit `Complexity.Machine` with a
  polynomial `Run` bound and removes a premise from one idea. They are
  independent small PRs and may proceed in parallel; the numbering is only a
  suggested priority:
  1. `CNFEvalInP` (Idea 06)
  2. `WitnessCheckInP` (Idea 09)
  3. `UnitSATInP` (Idea 18)
  4. `CoverCheckInP` (Idea 36)
  5. `IterationClosure` (Idea 40)
  6. `SeedEnumeration` (Idea 14)
  7. `SmallComponentSATInP` (Idea 25)
  8. `LogSeparatorSATInP` (Idea 26)

  `VCHard` (Idea 36) needs #624 and one more reduction.

## Later

- **Milestone C (#568).** Exact sharing of residual subproblems. Define the
  residual representation, canonicalization, key and termination measure.
  Prove merge soundness and a runtime bound over generated states with lookups
  charged. Test it against the families from Ideas 26 and 35 and from #567.
  Finish with a quantitative gain, a scoped theorem, or a certified
  counterexample family. Depends on Milestone B.
- **The `SuperpolyLowerBound SAT` frontier (#567).** For arbitrary
  well-formed NAND DAGs. Each proposal needs a barrier audit and separately
  falsifiable claims before work starts (RESEARCH_VISION.md, section 2).
- **Williams ingredients.** `NTimeHierarchy` through `LazyDiagonalSimulation`,
  then `EasyWitnessLemma`, then `WilliamsSpeedup`. Each is an independently
  reviewed piece. Adding corollaries that assume all three is not progress.
- **Multi-tape model extension.** A documented extension of the shared model
  with a proved simulation theorem. It is needed before porting any
  fine-grained bound (SETH-type statements, Williams savings).
- **Independence track.** Merge the three independence documents into one.
  Fix a target theory before any formal work.
- **Historical attempts.** Raise attempts that touch an open obligation to a
  source-level refutation or explicit conditional result. The order, the
  first 20 attempts and the definition of done are in
  [proofs/attempts/REFUTATION_PLAN.md](proofs/attempts/REFUTATION_PLAN.md).
  Then work through
  [literature/CLAIMED_PROOFS_2017_2026.md](literature/CLAIMED_PROOFS_2017_2026.md).

## Continuous

- **Monthly literature sweep.** Query the arXiv API
  (`https://export.arxiv.org/api/query?search_query=<query>&sortBy=submittedDate&sortOrder=descending&max_results=100`)
  with these query strings:
  - `cat:cs.CC AND (abs:"P versus NP" OR abs:"P vs NP" OR abs:"P != NP" OR abs:"P = NP")`
  - `cat:cs.CC AND (abs:"circuit lower bound" OR abs:"formula lower bound")`
  - `(cat:cs.CC OR cat:cs.DS) AND (abs:"exponential time hypothesis" OR abs:"SETH" OR abs:"k-SAT")`
  - `cat:cs.CC AND (abs:"proof complexity" OR abs:"resolution proof" OR abs:"resolution refutation")`
  - `cat:cs.CC AND (abs:"natural proofs" OR abs:"relativization" OR abs:"algebrization")`
  - `(cat:cs.LO OR cat:cs.CC) AND (abs:"Cook-Levin" OR abs:"formalization") AND (abs:Lean OR abs:Coq OR abs:Rocq)`

  Space the calls at least 3 seconds apart, as the arXiv API terms ask;
  back-to-back calls get HTTP 429. Also check ECCC and the openai/math and
  anthropics/formal-math repositories through `gh api`, without cloning
  them. Record new items in
  `literature/registry.json` following section 5 of RESEARCH_VISION.md.
- **Quarterly registry review.** Update review status of claimed results
  (for example the claimed ETH refutations), refresh pinned revisions, and
  update the dated notes in affected documents.
- **Weekly CI budget review.** Check run time and cache size of
  `verification.yml` and any external re-verification workflow. Move
  long-running jobs to manual dispatch.

## Definition of done

A milestone is done when its PR meets every item below. These combine the
acceptance rules of #567 (section 8) and #568 (section 7) with the
hypothesis-manifest rule of #629 and the issue-hygiene rule of the
2026-10-03 reopening comments.

1. **Paired statements.** Lean and Rocq statements with the same names and
   matching semantics. No new admissions or problem-specific axioms in the
   certified dependency closure.
2. **Assumption reports.** `#print axioms` and `Print Assumptions` output
   pasted in the PR, within the allowed sets. New results are listed in
   `scripts/proof_status.json`.
3. **Explicit hypotheses.** A separate list of every theorem argument that is
   an unproved premise, each registered in
   [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md). An empty assumption report
   does not discharge a theorem argument.
4. **Before and after.** The named premise removed, the concrete machine or
   cost bound, the all-size restricted theorem, or the certified family that
   refutes a precise candidate. Show both statements.
5. **Error review.** A check against
   [COMMON_ERRORS.md](proofs/attempts/COMMON_ERRORS.md) with concrete
   evidence: families 1, 7, 10-14, 16-18 and 20 for #567; families 2, 4-9,
   11-12, 15 and 17 for #568.
6. **Mutation and non-vacuity tests.** Fake zero costs, an oracle in place of
   a machine, weakened acceptance, invalid encodings, swapped quantifiers and
   an enlarged model class are rejected for semantic reasons.
7. **Result class and provenance.** One result class from #567: known
   theorem mechanized, algorithm-specific refutation, restricted-model lower
   bound, conditional general result, unconditional general result.
   Separately, one provenance label from #568: known theorem newly
   mechanized, new-to-repository engineering, new mathematical result, or
   conjecture. This repository adds a fifth label, known theorem reused, for
   a PR that only applies a result already mechanized here; it is a
   repository extension, not part of #568.
8. **Reproducibility.** Pinned tools, clean build commands, seeds and corpora
   for experiments. Measured performance is kept separate from proved bounds.
9. **Issue hygiene.** "Refs #N" for slices. "Fixes #N" only when the PR
   delivers that issue's whole deliverable. For #567 and #568 that means a
   closing theorem: a declaration whose type is exactly
   `Complexity.PNotEqualsNP` (#567) or `Complexity.PEqualsNP` (#568), with no
   arguments, certified in both provers. The PR shows the type with `#check`
   (Lean) and `Check` (Rocq) output, and its `#print axioms` and
   `Print Assumptions` output lists only the allowed axioms. The manifest
   cannot record theorem arguments, so this is checked on the type.
