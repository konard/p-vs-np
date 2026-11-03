# Literature registry

This directory is the repository's catalogue of external sources: papers, AI-lab
releases, formal proof artifacts, surveys, critiques and claimed P versus NP
proofs. It answers three questions for a contributor:

1. Which published result or artifact touches a hypothesis or obligation here?
2. Where exactly is it: which release, which file, which declaration?
3. What is it worth here: reported status, checked status, and whether it applies
   to this repository's machine model?

It implements the seed of issue
[#634](https://github.com/konard/p-vs-np/issues/634) and uses the claim-status
labels of issue [#635](https://github.com/konard/p-vs-np/issues/635). It
supplements, and does not replace, the [attempts catalog](../proofs/attempts/README.md),
the [error families](../proofs/attempts/COMMON_ERRORS.md), the
[formal statement](../FORMAL_STATEMENT.md), the
[hypothesis inventory](../proofs/HYPOTHESES.md) and the
[certified-result manifest](../scripts/proof_status.json).

The registry is a finite seed, compiled on 2026-11-03. It does not claim to
enumerate every public source.

## Files

| File | Role |
| --- | --- |
| [registry.json](registry.json) | The machine-readable registry. The only file to edit by hand when adding a source. |
| [REGISTRY.md](REGISTRY.md) | Generated table view. Never edit it by hand. |
| [CLAIMED_PROOFS_2017_2026.md](CLAIMED_PROOFS_2017_2026.md) | Human-readable backlog of claimed proofs after Woeginger's list. |
| [../scripts/check_literature_registry.py](../scripts/check_literature_registry.py) | Validator, offline query tool and renderer. |
| [../scripts/test_check_literature_registry.py](../scripts/test_check_literature_registry.py) | Unit tests for the checker. |

## The one rule: a source never changes a proof status

Adding, editing or upgrading a registry entry never changes the status of any
theorem in this repository. A paper, a Lean file that compiles upstream, an
Isabelle entry, a model-generated candidate and a search failure have different
evidentiary meaning, and none of them is a local certificate. Local status lives
only in [scripts/proof_status.json](../scripts/proof_status.json), under the
review rules in [scripts/README.md](../scripts/README.md). Named open premises
live in [proofs/HYPOTHESES.md](../proofs/HYPOTHESES.md).

The checker enforces part of this rule. A `locally-certified` entry needs a
`local_certificate` equal to a `theorem` in `scripts/proof_status.json`.
Claimed proofs cannot rise above `candidate`. `upstream-checked`,
`locally-replayed`, `conditional-bridge` and `locally-certified` need a
`formal` record whose `model`, `declaration`, `file` and `revision` are
recorded, not `unknown`, `not recorded` or `not applicable`. As of 2026-11-03
no entry is locally replayed, conditionally bridged or locally certified.

## Schema

`registry.json` is one JSON object:

```json
{ "schema_version": "1", "updated": "2026-11-03", "entries": [ ... ] }
```

Entries are kept sorted by `id`. Each entry has these fields.

### Required fields

| Field | Meaning |
| --- | --- |
| `id` | Stable kebab-case identifier, unique in the registry, for example `openai-2026-eth-false`. Never reuse or rename an id; other documents cite it. |
| `title` | Title of the work as published. Abbreviations are marked in the title. |
| `authors` | List of names. AI-authored work uses the lab form, for example `"Claude (Anthropic)"` or `"OpenAI (unnamed internal model)"`. |
| `year` | Year as an integer. Must match the first four characters of `date`. |
| `date` | `YYYY-MM-DD`, `YYYY-MM` or `YYYY`. Use the first public date of the version described. For arXiv rows without a recorded day, the month comes from the arXiv identifier. |
| `venue` | Where it appeared, with version and revision details. |
| `urls` | List of URLs. The first is the canonical primary URL and must be unique across the registry. Later URLs are mirrors, companion files or the containing repository. |
| `artifact_class` | `paper`, `machine-checked-proof`, `statement-only-benchmark`, `generated-candidate`, `code`, `dataset`, `model`, `survey`, `blog`, `critique`, `formalization-library` or `tool`. |
| `result_type` | `peer-reviewed-theorem`, `preprint-theorem`, `ai-lab-lean-checked`, `ai-lab-manuscript-only`, `claimed-p-vs-np-proof`, `survey`, `formalization-artifact`, `barrier-result` or `critique`. |
| `claim` | One or two sentences with the precise bound or statement. Where the manuscript and the formal statement differ, both are given. |
| `status` | The source's own review status: `peer-reviewed`, `under-expert-review`, `unreviewed-preprint`, `withdrawn`, `refuted`, `formally-checked` or `unknown`. `under-expert-review` is used only where a named public review process exists. |
| `claim_status_local` | The #635 label for this repository: `discovered`, `statement-only`, `candidate`, `upstream-checked`, `locally-replayed`, `conditional-bridge` or `locally-certified`. See below. |
| `relevance` | One to three sentences naming the hypothesis or obligation it touches. |
| `caveats` | What limits the claim or its use here. Never empty; write `None noted.` if nothing was found. |
| `tags` | Tags from the vocabulary below. |
| `verified` | `yes` if the researcher opened the primary URL and the title, authors and date matched; `partial` if one stated detail comes from a secondary source; `no` if the item, or a material fact in it, is unverified. |
| `added` | Date the entry was added, `YYYY-MM-DD`. |

### Optional fields

| Field | Meaning |
| --- | --- |
| `parent` | Id of the release or collection that contains this artifact. This gives the lineage paper or claim → release → artifact. |
| `formal` | Object describing the formal artifact: `prover`, `model` (for example `Mathlib Turing.FinTM2`, `custom word-RAM`, `call-by-value lambda-calculus L`, `multi-tape TM (Isabelle)`), `declaration`, `file`, `revision` (commit or release tag), `kernel_checks` (for example `["lean", "nanoda", "comparator"]`) and `axioms`. This gives the last lineage step, artifact → exact declaration. Unknown values are written `"unknown"`, except that `upstream-checked` and stronger labels need a recorded `model`, `declaration`, `file` and `revision`. |
| `license` | Component license, or `"unknown"`. Unknown means review is required before copying, not that the artifact is unavailable. One release can have different licenses for code, manuscripts, data and weights. |
| `size_note` | Approximate download size, only when sourced. |
| `local_obligation` | The local premise or obligation the source bears on, for example `SATHard (#624)`, `Idea 41: NTimeHierarchy, EasyWitnessLemma, WilliamsSpeedup (#629)`, or `none`. |
| `attempt_slug` | For claimed proofs: the suggested `proofs/attempts/<slug>/` folder name. |
| `claim_direction` | For claimed proofs: `peqnp`, `pneqnp`, `unprovable`, `undecidable`, `other`, `both` or `unknown`. |
| `common_errors_family` | For claimed proofs: the most likely [COMMON_ERRORS](../proofs/attempts/COMMON_ERRORS.md) family, 1 to 20. **This is a hypothesis** from the abstract and any published critique, not an audit. |
| `common_errors_secondary` | Further hypothesised families. |
| `existing_attempt` | An existing `proofs/attempts/` folder by the same author or on the same line. |
| `documented_responses` | List of `{ "url", "note" }`: critiques, withdrawals, author replies, expert posts. A `status` of `withdrawn`, `refuted`, `formally-checked` or `under-expert-review` needs this list or `notes` that cite the source. |
| `source_row` | Row number in the 2026-11-03 research table, for traceability. |
| `local_certificate` | Required only for `locally-certified`; must equal a `theorem` value in `scripts/proof_status.json`. Unused so far. |
| `notes` | Source conflicts, merges and other provenance. Where two sources disagree, both are recorded here. |

### Lineage from paper to declaration

Follow a result in four steps:

1. **Paper or claim.** The entry itself: `title`, `venue`, `urls[0]`.
2. **Release.** `parent`, for example `openai-2026-math-collection` or
   `anthropic-2026-formal-math`.
3. **Artifact.** The remaining `urls` and `formal.file`, pinned by
   `formal.revision` where known.
4. **Declaration.** `formal.declaration`, checked by `formal.kernel_checks`,
   with `formal.axioms`.

Worked example: `openai-2026-bin-packing-p-np` → parent
`openai-2026-math-collection` → file
`lean/OAI/Computability/BinPacking/Search/ApproximationImpliesP.lean:730` at
revision `4eaee87` → declaration
`OAI.BinPackingGap.PackingGapNPHard.pEqualsNP_of_absoluteAdditiveAlgorithm`.
Its statement file `lean/ComparatorChallenges/BinPackingGap.lean` contains
`sorry` by design. The proof location is a different file, and status checks
must run there (issue #635 comment of 2026-10-09).

### Claim-status labels (#635)

| Label | Meaning |
| --- | --- |
| `discovered` | Found and recorded. Nothing checked locally. |
| `statement-only` | A formal statement exists without a proof, for example a benchmark entry. |
| `candidate` | A proof candidate (model output, search hit) that nobody has checked. |
| `upstream-checked` | The upstream kernel check is reported, and the entry records the prover, model, declaration, file and pinned revision. Not replayed here. |
| `locally-replayed` | Replayed in a compatible local environment, with an import and axiom audit. |
| `conditional-bridge` | Replayed, but transfer to the local model depends on a named, missing bridge obligation. |
| `locally-certified` | The local conclusion is in `scripts/proof_status.json`. Never set by this registry alone. |

## Five separate attributes

Issue #634 asks that these be kept apart. One does not imply another.

| Attribute | Question | Where it is recorded |
| --- | --- | --- |
| `public` | Can anyone read it without an account? | Implied by an `https` URL that `verified: yes` opened. Paywalled DOIs are public metadata only. |
| `downloadable` | Can the artifact itself be fetched, not just described? | `urls`, `size_note`. A blog that describes a model is public but the model is not downloadable. |
| `open-source` | May it be copied and modified here? | `license`. `"unknown"` blocks copying until reviewed. A root license does not cover every component. |
| `formally checked` | Did a proof kernel accept a stated declaration? | `formal.kernel_checks`, `claim_status_local` (`upstream-checked` or stronger). |
| `applicable here` | Does the checked statement mean the same thing in this repository's model? | `formal.model`, `local_obligation`, `relevance`, and the `model-fidelity` tag. Only a local replay plus a proved bridge can make it so. |

### Why "kernel-checked upstream" is not "theorem here"

A kernel check proves that the encoded formal statement follows in that
environment. It does not show that the formal statement says what the paper
says, that its hypotheses are satisfiable, or that its definitions match ours.
This repository defines P and NP on a finite one-tape machine with charged
runs and explicit polynomial bounds ([proofs/complexity/README.md](../proofs/complexity/README.md)).
[FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md) relates the Clay statement to the
target `Complexity.PEqualsNP`. The sources in this registry use other models:

| Entry | Upstream model |
| --- | --- |
| `anthropic-2026-3sat-subexp` | Mathlib `Turing.FinTM2` (multi-stack) |
| `openai-2026-eth-false` | custom `PrimitiveMachine` multitape model on Mathlib `Turing.TM0` tapes |
| `openai-2026-bin-packing-p-np`, `openai-2026-cook-levin-tm2` | Mathlib `Turing.TM2ComputableInPolyTime` with a `FiniteAlphabet` side condition |
| `alman-vw-2026-3sum-apsp` | custom word-RAM in core Lean |
| `gaher-kunze-2021-cook-levin-coq` | call-by-value lambda-calculus L (Rocq) |
| `balbach-2023-cook-levin-isabelle` | multi-tape Turing machines (Isabelle/HOL) |
| `senellart-gnatenko-2026-descriptive-complexity-lean` | first-order reductions (descriptive complexity) |

A kernel-checked `PEqualsNP` in the OpenAI library is a different proposition
from `Complexity.PEqualsNP`. Treating matching names as matching meaning is
error family 11 of [COMMON_ERRORS](../proofs/attempts/COMMON_ERRORS.md)
("undefined, nonstandard, or incompatible formal definitions"). Model overhead
also matters: a single-tape simulation can destroy a subexponential saving. Any
use of an external theorem must name the bridge obligations (machine,
encoding, cost, reduction, uniformity) and enter them in
[proofs/HYPOTHESES.md](../proofs/HYPOTHESES.md) until they are proved.

## Tag vocabulary

The checker defines this vocabulary in `TAGS` and fails if this table differs.

<!-- tags:start -->
| Tag | Use for |
| --- | --- |
| `eth` | Exponential Time Hypothesis, its variants and refutation claims |
| `seth` | Strong Exponential Time Hypothesis |
| `sat-algorithms` | algorithms and exact bounds for SAT and k-SAT |
| `fine-grained` | fine-grained complexity (3SUM, APSP, exponential-time bounds) |
| `counting` | counting problems (#SAT, permanent) |
| `circuit-lower-bounds` | Boolean or quantum circuit lower bounds |
| `algebraic-complexity` | algebraic circuits, VP vs VNP, permanent vs determinant |
| `matrix-multiplication` | the matrix multiplication exponent |
| `gct` | geometric complexity theory |
| `proof-complexity` | proof systems and their lower bounds |
| `meta-complexity` | MCSP, learning and Kolmogorov-style meta-complexity |
| `kolmogorov` | time-bounded Kolmogorov complexity |
| `range-avoidance` | range avoidance and explicit constructions |
| `williams` | the Williams algorithms-to-lower-bounds route (Idea 41) |
| `derandomization` | derandomization of time or space |
| `space-time` | time-space simulations and space classes |
| `catalytic` | catalytic computation |
| `pcp` | PCPs, label cover and unique games |
| `hardness-of-approximation` | NP-hardness of approximation |
| `extended-formulations` | LP and SDP extended formulations |
| `reductions` | reductions and completeness results |
| `quantum` | quantum models |
| `barriers` | relativization, natural proofs, algebrization and other barriers |
| `independence` | claims about unprovability or undecidability |
| `formalization` | machine-checked artifacts and formal libraries |
| `lean` | Lean artifacts |
| `rocq` | Rocq (Coq) artifacts |
| `isabelle` | Isabelle artifacts |
| `cook-levin` | Cook-Levin theorem and SAT hardness (SATHard, #624) |
| `model-fidelity` | machine-model, encoding or cost-model mismatch risk |
| `tool` | verification or registry tooling |
| `ai-lab` | results or releases from AI labs |
| `expert-commentary` | blogs, statements and expert commentary |
| `survey` | surveys, textbooks and canonical references |
| `critique` | published critiques of claimed proofs |
| `claimed-proof` | claimed resolutions of P vs NP and related separations |
| `peqnp` | the claim is P = NP |
| `pneqnp` | the claim is P != NP |
<!-- tags:end -->

To add a tag, add it to `TAGS` in the checker and to this table in the same
change.

## Querying offline

All commands read only local files. Results are ordered by date, newest first,
then by id. Run them from the repository root.

```sh
python3 -I scripts/check_literature_registry.py                       # validate
python3 -I scripts/check_literature_registry.py --stats               # counts by type, status, year
python3 -I scripts/check_literature_registry.py --tag eth             # ETH sources
python3 -I scripts/check_literature_registry.py --tag sat-algorithms  # SAT algorithms
python3 -I scripts/check_literature_registry.py --tag reductions      # reductions and completeness
python3 -I scripts/check_literature_registry.py --tag circuit-lower-bounds --since 2024
python3 -I scripts/check_literature_registry.py --tag cook-levin --json   # full records
python3 -I scripts/check_literature_registry.py --type claimed-p-vs-np-proof --since 2025
python3 -I scripts/check_literature_registry.py --type machine-checked-proof
python3 -I scripts/check_literature_registry.py --status upstream-checked
python3 -I scripts/check_literature_registry.py --status withdrawn
python3 -I scripts/check_literature_registry.py --text permanent
python3 -I scripts/check_literature_registry.py --render              # regenerate REGISTRY.md
python3 -I scripts/check_literature_registry.py --check-render        # fail if REGISTRY.md is stale
python3 -I scripts/check_literature_registry.py --check-readme        # this guide and the backlog against the registry
```

Validation also checks this guide: the tag table, the `verified: no` list under
"Known gaps", and every backticked id-like token (kebab-case with a year) here
and in [CLAIMED_PROOFS_2017_2026.md](CLAIMED_PROOFS_2017_2026.md), which must
name a registry entry, an `attempt_slug` or a `proofs/attempts/` folder.

`--type` matches `result_type` or `artifact_class`. `--status` matches `status`
or `claim_status_local`. `--text` is a case-insensitive substring of the title
or claim. Filters combine with AND.

Tests:

```sh
python3 -I scripts/test_check_literature_registry.py -v
python3 -m unittest scripts.test_check_literature_registry -v
```

## Adding an entry

1. Pick a stable id: `author-year-topic` in kebab-case. For claimed proofs, use
   the attempt slug format `author-year-claim` of [proofs/attempts](../proofs/attempts/README.md).
2. Open the primary URL yourself. Set `verified` honestly. Record secondary
   facts as `partial` and say which detail is second-hand.
3. Fill every required field. Write `unknown` rather than guessing a license,
   a revision or a proof status.
4. Record the source's own status. Never set a status above what the source
   documents. A journal publication is `peer-reviewed` even when disputed; put
   the dispute in `documented_responses`.
5. For a formal artifact, fill `formal` with the exact, fully qualified
   declaration and file, and pin `revision` to a commit. Without them the entry
   stays at `discovered` or `statement-only`.
6. Run the validator, the tests and `--render`, and commit `registry.json` and
   `REGISTRY.md` together.

Adding a source never changes a proof status. If a source suggests that a
local premise is now false or provable, open an issue and update
[proofs/HYPOTHESES.md](../proofs/HYPOTHESES.md) through review. Do not edit
`scripts/proof_status.json` from a registry change.

## Intake procedure for a new paper or AI-lab release

1. **Registry entry.** Add the entry with `claim_status_local: discovered`.
   For a release, add a parent entry for the release and child entries for each
   materially different component (manuscript, formal library, data, weights).
2. **Relevance.** Name the hypothesis or obligation it touches in `relevance`
   and `local_obligation`.
3. **Fidelity audit.** Read the formal statement, not only the paper. Record
   the upstream machine model, encoding, cost model and side conditions in
   `formal.model` and `caveats`. Check statement and proof locations
   separately. Run `#print axioms` (Lean) or `Print Assumptions` (Rocq) on the
   exact declaration if you replay it.
4. **Bridge obligations.** List each missing equivalence or simulation between
   the upstream model and the local one. Enter it as a named premise in
   [proofs/HYPOTHESES.md](../proofs/HYPOTHESES.md) or as an issue.
5. **Optional CI re-verification.** A local replay of a narrow, pinned
   declaration can raise `claim_status_local` to `locally-replayed`, or to
   `conditional-bridge` when bridges remain. This belongs to issue #635.
6. **Dated notes.** Add a dated note to each affected document, for example
   "2026-11-03: ETH is claimed false (see literature registry
   `openai-2026-eth-false`); the premise remains open here".

## Review cadence

**Monthly arXiv and repository sweep** (first week of each month). Run these
queries with a date filter covering the last 35 days and triage as in
[CLAIMED_PROOFS_2017_2026.md](CLAIMED_PROOFS_2017_2026.md):

- arXiv titles:
  `https://export.arxiv.org/api/query?search_query=ti:%22P%20versus%20NP%22%20OR%20ti:%22P%20vs%20NP%22%20OR%20ti:%22P%3DNP%22%20OR%20ti:%22P%20%3D%20NP%22%20OR%20ti:%22P%20!%3D%20NP%22%20OR%20ti:%22P%20neq%20NP%22&sortBy=submittedDate&sortOrder=descending&max_results=100`
  (search string `ti:"P versus NP" OR ti:"P vs NP" OR ti:"P=NP" OR ti:"P = NP" OR ti:"P != NP" OR ti:"P neq NP"`).
- arXiv abstracts in cs.CC:
  `search_query=cat:cs.CC AND (abs:"P=NP" OR abs:"P = NP" OR abs:"P is not equal to NP" OR abs:"P is equal to NP" OR abs:"P \neq NP")`.
  Filter on phrases such as "we prove", "implies P=NP", "proof of".
- arXiv algorithm claims:
  `search_query=cat:cs.CC AND ti:polynomial AND (ti:3SAT OR ti:3-SAT OR ti:SAT OR ti:Hamiltonian OR ti:clique OR ti:"NP-complete" OR ti:TSP OR ti:coloring OR ti:"subset sum")`,
  repeated with `cat:cs.DS`, `cat:cs.DM`, `cat:math.CO`, `cat:math.GM`, `cat:cs.LO`, `cat:quant-ph`.
- arXiv rebuttals: `search_query=ti:critique AND cat:cs.CC`; also `ti:"refutation"`, `ti:"comment on"`, `ti:"evaluating the claims"`.
- arXiv serial authors: `au:Du_Lizhi`, `au:Lin_Tianrong`, `au:Chen_Yangjun`,
  `au:Gordeev_Lev`, `au:Jiang_Xinwen`, `au:Diaby`, `au:Arthanari`,
  `au:Tang_Jian_Gang`, `au:Lee_Changryeol`, `au:McCallum_Rupert`,
  `au:Barbosa_Andre`, `au:Feinstein`, `au:Kobayashi_Koji`, `au:Aslam_Javaid`,
  `au:Salum_Latif`, `au:Avramopoulos`; use `id_list=` to detect new versions.
- HAL:
  `https://api.archives-ouvertes.fr/search/?q=title_t:(%22P%20versus%20NP%22%20OR%20%22P%20%3D%20NP%22)&fl=title_s,authFullName_s,producedDate_tdate,uri_s,abstract_s&sort=producedDate_tdate%20desc&rows=100`.
- Zenodo (page size at most 25 anonymously):
  `https://zenodo.org/api/records?q=title:"P versus NP" OR title:"P vs NP" OR title:"P = NP" OR title:"P != NP" OR title:"P=NP" OR title:"P≠NP"&sort=mostrecent&size=25&page=N`.
- Crossref:
  `https://api.crossref.org/works?query.title=%22P%20versus%20NP%22&filter=from-pub-date:2026-10-01&rows=100`,
  repeated with "P = NP" and "P≠NP".
- For the non-claim parts of the registry, also check `https://arxiv.org/list/cs.CC/new`,
  ECCC, the Computational Complexity blog and ethdiscussion.blog.

**Quarterly revision and link check.** For every entry with a `formal.revision`
or a GitHub URL, check that the URL resolves, whether the upstream default
branch has moved, and whether the license or release has changed. Report stale
records in an issue. Never upgrade a status automatically; a moved revision
requires a renewed review.

**Event-triggered review.** A new AI-lab release, a new version of a tracked
claim, a withdrawal, a working-group verdict or a peer-review decision triggers
the intake procedure for the affected entries within a week.

## Retrieval rules

- Never clone multi-gigabyte repositories. `openai/math` is 940,236 KB packed
  at commit 4eaee87 (gh api repository size, 2026-11-03; see issue #633 for the
  selective-retrieval plan). Record any size with the revision and the date it
  was read.
- Fetch single files with `gh api` and pin the revision:
  `gh api 'repos/openai/math/contents/lean/docs/378.md?ref=<commit>' -H 'Accept: application/vnd.github.raw'`.
  List a directory with `gh api repos/openai/math/contents/lean/docs --jq '.[].name'`.
- Record a size in `size_note` only when a source states it.
- Do not commit PDFs, datasets, proof archives, checkpoints or weights.
  Link them.
- Downloaded files are untrusted. Keep them outside the repository, and run any
  script that reads them with `python3 -I`.

## Current headline items (as of 2026-11-03)

- `openai-2026-eth-false`: claims ETH, SETH, Gap-ETH and NSETH are false. Claimed, Lean-checked in its own model (weaker bound than the manuscript), under expert review at ethdiscussion.blog, not peer-reviewed. Does not settle P vs NP.
- `anthropic-2026-3sat-subexp`: claims 3-SAT in time 2^{O(n log log n / sqrt(log n))}, so ETH is false. Claimed, Lean-checked on Mathlib `Turing.FinTM2`; an unreviewed preprint, since no named expert review covers it. Does not settle P vs NP.
- `ethreview-2026-working-group`: the public review of the OpenAI ETH claim, organised by Impagliazzo, Paturi and Williams; Francis Zane wrote later posts. The Anthropic claim appears there only in reader comments. No verdict was found as of 2026-11-03. The organisers state that their involvement is not a certification.
- `alman-vw-2026-3sum-apsp`: claims truly subquadratic 3SUM and truly subcubic APSP. The paper states that Claude found the algorithm. Unreviewed preprint; Lean check on a custom word-RAM.
- `dias-lima-2026-limits-constants` and `majdoddin-2026-crossovers`: the crossover points are astronomically large; the claimed refutations have no practical algorithmic content.
- `mit-hardness-2026-eth-dead-sh`: proposes SH, equivalent to Weak ETH, as the replacement assumption. Unreviewed preprint.
- `openai-2026-ugc`: claims a proof of the Unique Games Conjecture, with Lean-checked reductions. Unreviewed; human vetting ongoing.
- `openai-2026-border-dc-permanent`: claims an Omega(n^3) border determinantal complexity lower bound for the permanent. Unreviewed; Lean-checked with explicit constants.
- `braun-2026-bitphp-resxor`: first exponential lower bound for DAG-like Res(xor). Unreviewed preprint; Lean formalization reported but not inspected.
- `williams-2025-sqrt-space`: TIME[t] in SPACE[sqrt(t log t)] for multitape machines. Peer-reviewed.
- `openai-2026-bin-packing-p-np`: a kernel-checked `PEqualsNP` statement in a different model; the reference example for model mismatch.
- `xu-zhou-2023-sat-exhaustive-search`: a P != NP claim published in a journal and disputed by two published critiques, including Allender and Williams.

None of these changes a proof status in this repository.

## Known gaps

- viXra and ResearchGate were not covered. Preprints.org returned HTTP 403, so
  its rows rely on search snippets. cstheory.stackexchange could not be fetched.
- Entries with `verified: no`: `konstantinos-kyritsis-2019-unknown` (direction),
  `bryn-morgan-2025-unknown` and `matthew-hall-2025-unknown` (direction from
  title only), `toct-2021-incident-peqnp` (author),
  `shoenfield-1961-absoluteness` (original paper not opened).
- Other Zenodo rows are `partial`: their claim direction comes from the title
  only.
- Several venue claims rest on search results only (`ren-wang-zhong-2025-range-avoidance`,
  `joshi-tal-vasconcelos-wright-2025-qac0`, `garlik-et-al-2026-meta-math-algebraic`).
  They are recorded as preprints until confirmed.
- The OpenAI families 102, 103, 105-108, 112, 118, 126, 135, 137 and 274 record
  fully qualified Comparator declarations read at commit 4eaee87 on
  2026-11-03. Their proofs under `lean/OAI/` were located only for 118 and the
  Cook-Levin development; the others rely on the upstream Comparator check.
  Families 132 and 133 are recorded as `statement-only`.
- Every `upstream-checked` entry pins `formal.revision`. Re-checking the pins
  is the first task of the quarterly check. `cslib-2025` and
  `tsoukalas-2026-alphaproof-nexus` record no single declaration and stay at
  `discovered`.
- The #634 seed families outside complexity theory are not yet recorded:
  OpenAI `ten-proofs`, miniF2F and GPT-f; DeepMind AlphaProof IMO outputs and
  AlphaGeometry 1 and 2; MathComp, CoqGym and Metamath set.mm; NuminaMath-LEAN,
  ProofNet, Lean Workbook and LEAN-GitHub; LeanDojo-v2, LeanSearchClient,
  DeepSeek-Prover-V2 and Goedel-Prover. See
  [the issue #634 seed table](https://github.com/konard/p-vs-np/issues/634).
- Licenses are `unknown` for almost every paper. Repository licenses were read
  with `gh api` on 2026-11-03 for openai/math, anthropics/formal-math,
  leanprover/comparator, leanprover/cslib, PierreSenellart/descriptive-complexity
  and google-deepmind/alphaproof-nexus-results (all Apache-2.0).
