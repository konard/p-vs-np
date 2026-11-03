# Research vision

This document states, in one place, how this repository does research on
P versus NP. Every contributor and every AI agent should work by these rules.
[ROADMAP.md](ROADMAP.md) gives the ordered work plan; this file gives the
method behind it. The rules for day-to-day work are in
[CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md).

Status notes are as of 2026-11-03, for `main` at `ecedd2b` unless an open
PR is named. **No resolution of P versus NP is claimed or promised.**

## 1. The goal and what "solved" means here

The question is the Clay Millennium Problem ([`pvsnp.pdf`](pvsnp.pdf)). Inside
the repository it is the pair of formal statements `Complexity.PEqualsNP`
(`∀ L, InNP L → InP L`) and `Complexity.PNotEqualsNP` (`¬ PEqualsNP`). They
are defined once, in [`proofs/complexity/`](proofs/complexity/README.md), for
Lean, Rocq and Agda. [FORMAL_STATEMENT.md](FORMAL_STATEMENT.md) relates them to
the Clay statement. It also lists the modeling choices a reader must accept,
draws the result graph, and says what counts as solved.

There are three possible outcomes. None of them is claimed.

1. A certified theorem `Complexity.PEqualsNP`.
2. A certified theorem `Complexity.PNotEqualsNP`.
3. A certified independence result relative to a stated theory: a proof that a
   named theory, with a fixed encoding of the statement, proves neither side.
   P versus NP is an arithmetic statement. The clocked-SAT forms in
   [`proofs/experiments/issue7`](proofs/experiments/issue7/README.md) make this
   explicit. Forcing over set theory therefore cannot change its truth value,
   so an independence result must name a theory, usually a fragment of
   arithmetic.

"Certified" has a fixed meaning. The theorem must be stated with the same name
in Lean and Rocq and be listed in
[`scripts/proof_status.json`](scripts/proof_status.json). Its assumption
report may contain only `propext`, `Classical.choice` and `Quot.sound` in Lean,
and at most `Classical_Prop.classic` in Rocq.

A solution is a certified theorem whose type is exactly
`Complexity.PEqualsNP` or `Complexity.PNotEqualsNP`, with no arguments. The
manifest records only `source`, `theorem` and `allowed_axioms`, so it cannot
see theorem arguments. The PR therefore pastes the `#check` output (Lean) and
the `Check` output (Rocq) that show the type, and the `#print axioms` and
`Print Assumptions` output, which must list only the allowed axioms above. The
model-fidelity theorems of FORMAL_STATEMENT.md must be proved or listed there
as assumed. A theorem that takes `SATHard` or a similar argument is a
conditional result, even when it is certified. It is not a solution.

As of 2026-11-03 the certified results on `main` (78 per prover) include
P ⊆ NP for the shared model (`Complexity.pSubsetNP`) and SAT ∈ NP
(`SATVerifier.satInNP`). The main open premise is the NP-hardness of SAT
(`SATHard`).

## 2. Principles

**Formal first.** A result counts only when it is machine-checked. It must be
stated in Lean and Rocq with identical names. It may use no `sorry`, `admit`,
`Admitted`, `axiom`, `Axiom`, `Parameter`, `native_decide` or similar escape
hatch in its dependency closure, and no global axiom beyond the allowed ones
of section 1. Every unproved ingredient is an explicit theorem argument of
type `Prop`, defined once and registered in the hypothesis manifest
[proofs/HYPOTHESES.md](proofs/HYPOTHESES.md). The certified manifest
`scripts/proof_status.json` is the only list of results the repository
stands behind. A file that compiles but is not in that manifest is not
certified. Historical attempt reconstructions in `proofs/attempts/` may keep
documented admissions. Nothing certified may import them.

**One shared model.** There is exactly one definition of machines, runs,
polynomials, P and NP: `proofs/complexity/{lean,rocq,agda}`. There is one SAT
language, `Issue532.Machines.SAT`, with its encoding `encodeCNF`. New work
imports these; it never defines a second P, NP or SAT. A theorem proved in
another formal model (Gäher-Kunze's Cook-Levin in Rocq, Mathlib's `TM2`
machines in openai/math or anthropics/formal-math) is not a theorem here
until a checked simulation connects the two models. Known facts that relate
our single-tape model to textbook models, such as polynomial equivalence with
multi-tape and RAM machines, are not mechanized. FORMAL_STATEMENT.md
section 3 lists them as assumed, and proofs/HYPOTHESES.md names them as the
open premises `ModelEquivalence` and `EncodingInvariance`, which are not yet
defined in Lean or Rocq. They are never used silently. Legacy frameworks that still define their own P and NP
(`proofs/p_eq_np/`, `proofs/experiments/{lean,rocq}/PvsNPProofAttempt.*`) are
scheduled for retirement in #627 and must not be imported.

**Evidence classes.** Every result is reported in one of five classes, taken
from #567 (section 8):

| Class | Example in this repository |
| --- | --- |
| Known theorem mechanized | `satInNP`; `pSubsetPPoly` (PR #632) |
| Algorithm-specific refutation | `coarseKey_not_satisfiability_complete` (one memoization key) |
| Restricted-model lower bound | none certified yet. Idea 28 names Haken's resolution bound as `ResNotPolyBounded` and derives it only from the open `ERNotPolyBounded` |
| Conditional general result | `pEqualsNP_of_inP_sat` (premise `SATHard`) |
| Unconditional general result | none for P versus NP |

A PR also states its literature provenance, separately from its class. #568
(section 7) gives four labels: known theorem newly mechanized,
new-to-repository engineering, new mathematical result, or conjecture. This
repository adds a fifth, known theorem reused, for a PR that only applies a
result already mechanized here; it is a repository extension, not part of
#568, and #629 should define both vocabularies once. Claim "new mathematical
result" only after the prior-art comparison of this section. Analyses of
historical attempts use the four evidence levels of
[COMMON_ERRORS.md](proofs/attempts/COMMON_ERRORS.md): concrete refutation,
conditional result, identified gap, informal/unverified analysis. Idea
dossiers use the four verdicts of the
[research log](proofs/experiments/issue532/RESEARCH_LOG.md). These
vocabularies are not interchangeable. Do not upgrade a label to sound
stronger.

**Refute before build.** A new idea is first tested against what is already
known to fail: the 20 error families of COMMON_ERRORS.md, the 41 dossiers in
`proofs/experiments/issue532/ideas/`, the 116 attempt folders in
`proofs/attempts/`, and the
[vacuity report](experiments/issue532_vacuity/REPORT.md). That report found
that 25 of the 30 ideas that defined an obligation in the first version were
vacuous as stated: a free cost or class parameter made them provable or refutable in
one line. So every new obligation needs non-vacuity and mutation tests. Fake zero costs,
an oracle in place of a machine, weakened acceptance, invalid encodings and
an enlarged model class must be rejected for semantic reasons. Renaming a
symbol is not a test.

**Barrier audit.** Every proposal for a general lower bound states what
happens under relativization (Baker-Gill-Solovay), natural proofs
(Razborov-Rudich: constructivity, largeness, usefulness, and the exact
pseudorandomness assumption) and algebrization (Aaronson-Wigderson). The
barriers constrain specific kinds of arguments, not all mathematics. A
restricted-model result may stay inside a barrier if its scope is labeled.
The repository's abstract forms of these barriers are in Ideas 16, 30 and 38
and in `proofs/experiments/issue609/` (`KnownBarriers`). The oracle
constructions themselves are named hypotheses (`BGSCollapse`,
`BGSSeparation`), not proved.

**Prior art first.** Before writing a new lemma, search in this order: local
declarations, the research log and dossiers, `proofs/attempts/` and
COMMON_ERRORS.md, proofs/HYPOTHESES.md and the open issues, the literature
registry ([literature/REGISTRY.md](literature/REGISTRY.md),
[literature/registry.json](literature/registry.json)), then primary papers
and external libraries. Log the search and decide `reuse`, `adapt`, `reject` or `defer`. Absence from
this repository does not make an idea new. The procedure, the log fields and
the stopping rule are in CONTRIBUTING.md (from #636).

**External results are data, not theorems.** A kernel check establishes that
a formal statement follows in that environment. It does not establish that
the statement matches the paper, that it applies to our model, or that the
paper is correct. Two recent episodes show what this means in practice.

- On 2026-10-06 openai/math published 722 AI-generated manuscripts in 372 families; at commit `4eaee87` (2026-10-30) the catalogue lists 721 in 373 families. They
  include Lean-checked restricted lower bounds (families 108, 112, 126, 132,
  133, 135) and a claimed Lean-checked proof of NP-hardness of
  approximating Vertex Cover within 2−ε and of a Unique Games gap
  reduction (family 102). Some manuscripts have since been withdrawn. Where
  a machine model is used it is not ours: Mathlib `TM2` for family 102 and a
  custom multitape machine for family 112. The issue comments on #567 and #568 (2026-10-07)
  record what may be cited and how.
- On 2026-10-26 and 2026-10-27 OpenAI (openai/math family 378) and Anthropic
  (anthropics/formal-math, `eth/`) published Lean-checked claims that the
  Exponential Time Hypothesis is false: a deterministic #k-SAT algorithm in
  time roughly `2^{O_k(n·polyloglog n/√log n)}`. As of 2026-11-03 neither is
  peer reviewed. Impagliazzo, Paturi and Williams are reviewing the OpenAI
  claim; the Anthropic claim has no announced outside review as of
  2026-11-03. ETH implies P ≠ NP (PR #639, an unmerged draft, proves this
  over the shared model), and the converse is not known. So the claim does not settle P versus NP in either
  direction. A subexponential upper bound is not a polynomial one, so
  a refutation of ETH is not known to imply P = NP.

In both cases the repository records the claim in the literature registry,
audits statement fidelity, names the missing bridges and, where useful,
re-checks the upstream proof in CI. It does not import the theorem.

**Honest reporting.** PRs that deliver a slice of a track issue say
`Refs #N`, never `Fixes #N`. "Fixes #568" in PR #622 auto-closed #568 after
one slice, and #567 was closed by hand after the first slice (PR #623, which
said "Refs #567"). Both had to be reopened. Status notes carry a date.
External claims are labeled "claimed, unreviewed" until review ends. Theorem
counts, lines of code, CI runs and benchmark speed are not progress toward the
answer. Progress is a premise discharged, an obligation refuted, or a scoped
theorem whose class is stated.

## 3. The two tracks and their exchange contract

Two issues own the mathematics. Neither assumes the answer.

### 3.1 Constructive track: NP ⊆ P (#568)

The goal is one finite machine `m` and one polynomial `p`, fixed independently
of the input, with `DecidesWithin m p SAT`: every input word, SAT and UNSAT,
measured in encoded bit length, with all costs charged. Together with a proved
`SATHard`, this gives `Complexity.PEqualsNP`. No advice, oracle, free
preprocessing, unit-cost arithmetic on unbounded numbers, or restriction to
favourable instances is allowed.

- **Milestone A: Cook-Levin hardness (`SATHard`) in the shared model** (#624).
  The bounded tableau (`Issue568.Tableau`: `localTrace_iff_run`,
  `boundedAccept_iff_run`) is on `main` (PR #622). PR #630 adds #624's
  slices 1-2 (of 4): the CNF of a bounded verifier run (`tableauCNF_iff`)
  and its encoded-size bound. The reduction as a `Complexity.Machine` with a
  polynomial `Run` bound, and the assembly of `satHard`, are missing.
- **Milestone B: a charged baseline.** `Issue8.NPSubsetP` proves DPLL correct
  (`dpll_correct`) and bounds its calls by `2^(|w|+1)` (`dpllSAT_calls_le`).
  No `Complexity.Machine` implements DPLL yet, so there is no `Run`-level
  cost to measure improvements against.
- **Milestone C: one falsifiable improvement.** The suggested candidate is
  exact sharing of residual subproblems (Ideas 22, 25, 26, 35, 40). Not
  started. #567 has already ruled out one key design
  (`coarseKey_not_satisfiability_complete`).

### 3.2 Lower-bound track: NP ⊈ P (#567)

The goal is one fixed language in NP and outside P. A sufficient target
already exists with no premise:
`∀ m p, ∃ x, clockCheck m p x = false` implies `PNotEqualsNP`
(`Issue7.ClockedSAT.pNotEqualsNP_of_pi2`). Proving the per-machine form with
a language chosen for each machine is not progress:
`per_machine_form_holds` proves that weaker form outright.

- **N1: `CircuitSATInNP`** (#625). PR #631 proves `circuitSATInNP` with an
  83-state verifier. CI is green and the PR has been reviewed.
- **N2: `PSubsetPPoly`** (#626). PR #632 proves `pSubsetPPoly` by compiling
  clocked machines into NAND circuits. CI is green and the PR has been
  reviewed.
- **N3: all-size, scope-correct results from candidate failures.** One scoped
  result exists (`coarseKey_not_satisfiability_complete`). The named next
  step, extracting a `ResDerives` certificate from a Davis-Putnam run
  (Idea 27, reusing Idea 28), has not been started.
- **The frontier.** For the circuit route the target is
  `SuperpolyLowerBound SAT` (Idea 30) for arbitrary well-formed NAND DAGs.
  Shannon counting, monotone circuits or formulas do not suffice. For the
  machine route the target is a real invariant valid for every machine.
  "Every algorithm must search all witnesses" is the missing result, not a
  starting assumption.
- **Williams bridge** (Idea 41). `FastCircuitSAT` together with
  `NTimeHierarchy`, `EasyWitnessLemma` and `WilliamsSpeedup` gives
  NEXP ⊄ P/poly. That is not known to imply P ≠ NP. Refuting
  `FastCircuitSAT` gives P ≠ NP once `CircuitSATInNP` is proved, but that is
  itself a major lower bound. Model overhead matters here: a single-tape
  simulation can destroy a `2^n/n^{ω(1)}` saving.

### 3.3 Result graph and what each premise blocks

| Edge to the target | Theorem | Premise on `main` | Status as of 2026-11-03 |
| --- | --- | --- | --- |
| `PEqualsNP → InP SAT` | `SATVerifier.inP_sat_of_pEqualsNP'` | none (`SATInNP` discharged by `satInNP`) | proved |
| `InP SAT → PEqualsNP` | `pEqualsNP_of_inP_sat` | `SATHard` | #624; PR #630 partial, CI red |
| Π⁰₂ clocked SAT `→ PNotEqualsNP` | `pNotEqualsNP_of_pi2` | none | proved |
| NP ⊄ P/poly `→ PNotEqualsNP` | `npNotSubsetP_of_not_npSubsetPPoly` | `PSubsetPPoly` | removed by PR #632 once merged |
| `¬ FastCircuitSAT → PNotEqualsNP` | `pNotEqualsNP_of_not_fastCircuitSAT` | `CircuitSATInNP` | removed by PR #631 once merged |
| `FastCircuitSAT →` NEXP ⊄ P/poly | `williams_method` | `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup` | open (#629) |
| ETH `→ PNotEqualsNP`, SETH `→ PNotEqualsNP` | `pNotEqualsNP_of_eth`, `pNotEqualsNP_of_seth` | not on `main`; no premise (uses the proved `satInNP`) | PR #639, overclaims to fix |

`SATHard` blocks most "algorithm implies P = NP" theorems in the repository,
including Ideas 01, 14, 32, 37 and 40 and the issue 7, 8 and 609 bridges.
Idea 36 instead takes `VCHard` and `CoverCheckInP`, so #624 alone does not
unblock it. `SATHard` also blocks the converse direction of the Π⁰₂
equivalence. Once PRs #631 and #632 are merged, the circuit routes of the
lower-bound track connect to the target with no premise except the lower
bound itself. That lower bound is the
open problem.

### 3.4 Exchange contract

- #568 supplies versioned algorithms, invariants, cost recurrences and
  explicit structural claims.
- #567 supplies minimized counterexamples, infinite hard families and
  scope-correct lower-bound arguments against them.
- Each counterexample names the exact claim and version it defeats. A failed
  candidate refutes that candidate, not P = NP. A failed lower-bound argument
  is not evidence for P = NP.
- A worst-case SAT or Circuit-SAT speedup is also checked against the
  Williams route, keeping exact parameters. A CNF speedup does not
  automatically give the circuit budget, because reductions add variables.
- Both tracks share one machine, SAT, circuit and tableau infrastructure.
  Two bounded-window layers (`Issue626.Window` in PR #632 and
  `Issue624.FixedWindow` in PR #630) are a known duplication to resolve.

## 4. How we treat previous attempts

[`proofs/attempts/`](proofs/attempts/README.md) holds 116 folders covering
claimed proofs from 1986 to 2016. All are indexed in COMMON_ERRORS.md. As of
2026-11-03 the evidence levels are: 2 concrete refutations
(`guohun-zhu-2007-peqnp`, `sergey-gubin-2010-peqnp`), 2 conditional results,
1 identified gap, and 111 informal/unverified analyses. Most of the catalog
is therefore a reading guide, not a set of checked refutations.

The plan is to raise attempts one at a time either to a **source-level
refutation** (the paper's exact proposition, with its input conditions, and a
checked witness that meets them and falsifies it) or to an **explicit
conditional result** (what the argument proves once its unproved step is a
named premise). A theorem about a simplified model, or one ending in `True`, does not count.
Attempts that touch an open obligation of the two tracks come first, for
example claimed polynomial SAT algorithms that can be stated over the shared
model.

Claims made after 2016 are listed in
[literature/CLAIMED_PROOFS_2017_2026.md](literature/CLAIMED_PROOFS_2017_2026.md).
They form a backlog for the same treatment. They are not folders yet.

Our own ideas get the same treatment. The first version of the 41 ideas
compiled and claimed conditional results, yet 25 of the 30 ideas with an
obligation were vacuous (section 2). After the machine refactor every obligation is stated
over `Complexity.Machine` and `Run`, each file proves that its obligation does
not hold for every language, and the trivializing proofs are kept as a
regression that must fail. Any new obligation needs the same protection.

## 5. How we take in new results

When a new paper, preprint or AI-lab release looks relevant, follow these
steps in order. Stop at any step that shows the result is irrelevant, and
record that decision.

1. **Registry entry.** Add a record to `literature/registry.json` with a pinned
   revision, artifact class, reported status ("claimed, unreviewed" by
   default), license state and retrieval method. Fetch single files with
   `gh api` or a sparse checkout. Do not clone large repositories.
2. **Relevance.** Name the hypotheses, obligations, ideas or attempts it
   touches. If none, record "not applicable" and stop.
3. **Fidelity audit.** Compare the paper's statement, the upstream formal
   statement and our definitions line by line. Check the machine model, the
   alphabet, the encoding, the cost measure, the size parameter, quantifier
   order and uniformity.
4. **Bridge obligations.** Name each missing simulation or equivalence as a
   `def … : Prop` registered in proofs/HYPOTHESES.md. The result then enters
   the repository only as a conditional theorem with that premise.
5. **Optional CI re-verification.** If the upstream proof is formal and
   relevant, re-check it in a separate CI workflow at a pinned commit, with
   the checker scripts archived and their output asserted. A re-verified
   upstream proof is still not a certified result of this repository.
6. **Dated notes.** Add a dated note to each affected document, with the
   claim label and a link to the registry entry.

What not to do:

- import a theorem by name from another machine model;
- treat a Lean kernel pass as peer review or as proof of statement fidelity;
- treat a failed search, a timeout or a type mismatch as a refutation;
- run multi-gigabyte clones or multi-hour builds on a development machine. A
  shallow clone of openai/math, taken without a pinned revision, filled a
  development disk during the 2026-10-07 review (#633). On 2026-11-03 GitHub
  reported a packed size of 940,236 KB for it at `4eaee87`. Record any size
  with a revision and a date.

## 6. What would change our direction

Stated in advance, so that each outcome has a defined effect on the plan.

- **Milestone C fails.** If the residual-sharing lemma is refuted for every
  canonicalization in the specified class, by a certified infinite family
  that forces superpolynomially many distinct residuals with lookups
  charged, we drop the candidate and record the result as an
  algorithm-specific refutation. A replacement candidate must first state its
  delta against the 41 dossiers and the primary literature.
- **Lower-bound proposals keep failing barrier audits.** If every proposed
  measure for `SuperpolyLowerBound SAT` fails the relativization,
  natural-proofs or algebrization audit, we put the lower-bound effort into
  the Williams ingredients (`LazyDiagonalSimulation`, `EasyWitnessLemma`,
  `WilliamsSpeedup`) and into restricted-model N3 results.
- **The bridges land.** When #631 and #632 merge, the negative track's
  priority moves from bridges to N3 and the frontier. When #624 completes,
  `pEqualsNP_of_inP_sat` and the "algorithm implies P = NP" theorems that
  take `SATHard` can be restated without that premise. Theorems with other
  premises stay conditional on them: Idea 14 (`NPinRP`, `SeedCompression`,
  `SeedEnumeration`), Idea 40 (`IterationClosure`), and Idea 36, which takes
  `VCHard` and `CoverCheckInP` instead of `SATHard`.
- **The ETH refutation survives review.** The target and the premises of both
  tracks do not change. Dossier text changes as follows.
  - Ideas 01 and 17: the passages on ETH and SETH get a note that ETH is
    refuted, with the reference.
  - Ideas 25 and 26: the "under ETH, no `2^{o(n)}` (or `2^{o(√n)}`) algorithm"
    statements stop counting as evidence that their obligations are hard.
  - Idea 37: "at least as hard as refuting ETH" stops being a hardness
    argument. The obligation still implies P = NP under `SATHard`, so it
    stays open.
  - Idea 41: both labs also claim a circuit lower bound for `E^NP`, argued
    informally and not formalized upstream. It is recorded in the dossier as
    a candidate application of the algorithmic method. It does not give
    `FastCircuitSAT` for general circuits and becomes no premise here.
  If the claim fails review, the dated notes record that and the dossiers
  keep their original wording.
- **A ported result needs a different model.** If a planned port needs
  multi-tape or RAM costs to keep its bound, we first prove a documented
  extension of the shared model and its simulation theorem. We do not port
  the result into the single-tape model with a hidden squared runtime.
- **Agent work turns into wrappers.** If PRs on a track add corollaries that
  assume the same open premises without discharging any, we stop that line
  and return to the next premise in ROADMAP.md.

## 7. Open questions about the program itself

Unresolved decisions about how the repository works, not about the mathematics.

- **Single-tape overhead.** The shared model is a one-tape machine. That is
  harmless for membership in P, but it can square running times. That matters
  for fine-grained statements such as SETH (the 2026-11-03 review of PR #639
  points out that SETH over this model may be weaker than the RAM version)
  and for Williams-type savings. A documented multi-tape extension, with its
  simulation theorem, is probably needed. Its design is open.
- **No Mathlib.** The Lean side uses core Lean only. That keeps builds small
  and audits simple. It also means Mathlib-based external results
  (openai/math, anthropics/formal-math, DescriptiveComplexity) cannot be
  replayed inside the library. #639's item P8 is blocked for this reason. One
  option is a separate Lake package with Mathlib for bridge work, kept out of
  the certified core. No decision has been made.
- **Cost of CI.** `verification.yml` selects jobs by changed paths. The
  external re-verification in PR #639 runs for hours and stores multi-gigabyte
  caches. We need a budget and a rule for what runs on every PR, on a
  schedule, or only by manual dispatch.
- **Whether to adopt CSLib.** A shared Lean library for computer-science
  foundations could reduce duplicated machine and reduction infrastructure.
  It would likely bring a Mathlib dependency and a different machine model,
  so adopting it would need the same bridge discipline as any external
  source. Not evaluated yet.
- **The paired-prover rule.** Rocq pairing roughly doubles the proof effort.
  Agda checks the shared model and five other small files, and has no
  manifest entries. Whether Agda should grow or stay minimal is open.
- **Independence work.** Three overlapping documents cover this track
  (the most current is
  [PROVING_P_VS_NP_UNDECIDABILITY.md](PROVING_P_VS_NP_UNDECIDABILITY.md)),
  and no target theory has been fixed.
- **Effort on historical attempts.** Raising 111 informal analyses to checked
  form is a large job with uncertain value. How to rank it against premise
  discharge is open.
- **Measuring progress.** The repository needs a measure other than theorem
  counts. One proposal: the number of open entries in proofs/HYPOTHESES.md
  and the number of attempts with checked evidence.

## Related documents

[FORMAL_STATEMENT.md](FORMAL_STATEMENT.md),
[proofs/HYPOTHESES.md](proofs/HYPOTHESES.md), [ROADMAP.md](ROADMAP.md),
[literature/README.md](literature/README.md),
[CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md).
