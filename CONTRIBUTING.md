# Contributing to P vs NP Research Repository

Thank you for your interest in contributing. This is a research repository
with machine-checked definitions and partial results about P versus NP. No
resolution is claimed. SAT ∈ NP is proved (`SATVerifier.satInNP`); the
NP-hardness of SAT (`SATHard`) is the main open premise (as of 2026-11-03).

Read [RESEARCH_VISION.md](RESEARCH_VISION.md) for the method and
[ROADMAP.md](ROADMAP.md) for the work order. [AGENTS.md](AGENTS.md) (the same
text as `CLAUDE.md`) is the short rule sheet for AI agents and humans. This
file gives the procedures.

## Adding New Proof Attempt Formalizations

When adding a new formalization of a P vs NP proof attempt, follow these guidelines to minimize merge conflicts and ensure CI passes.

### Directory Structure

Create your formalization in:
```
proofs/attempts/<author-year-claim>/
├── README.md              # Overview of the attempt and identified errors (REQUIRED)
├── original/              # Original proof idea and paper reconstruction (preferred)
│   ├── README.md          # Description of the original approach
│   ├── ORIGINAL.md        # Markdown reconstruction of the original paper
│   └── ORIGINAL.pdf       # Original paper PDF (or .html/.tex)
├── proof/                 # Forward proof formalization (recommended)
│   ├── README.md          # Explanation of proofs
│   ├── lean/              # Lean 4 formalizations
│   │   └── ProofAttempt.lean
│   └── rocq/              # Rocq formalizations
│       └── ProofAttempt.v
└── refutation/            # Refutation formalization (recommended)
    ├── README.md          # Explanation of failures
    ├── lean/              # Lean 4 formalizations
    │   └── Refutation.lean
    └── rocq/              # Rocq formalizations
        └── Refutation.v
```

**File descriptions:**
- **README.md** (required): Overview of the proof attempt, including metadata (author, year, claim), summary of the approach, and explanation of why it fails
- **original/README.md** (recommended): Description of the original proof idea and source material
- **original/ORIGINAL.md** (recommended): Markdown conversion/reconstruction of the original paper text, translated to English if needed
- **original/ORIGINAL.pdf** (recommended): The original paper in PDF format (or .html/.tex if PDF unavailable)
- **proof/**: Contains the forward proof formalization (attempting to follow the original author's approach)
- **refutation/**: Contains the refutation formalization (showing why the proof fails)

Older attempts may still keep root-level `ORIGINAL.*` copies for compatibility.

You can validate your attempt structure by running:
```bash
python3 scripts/check_attempt_structure.py --path proofs/attempts/<your-attempt>/
```

To generate a markdown list of all attempts without network access (the form
used in [scripts/README.md](scripts/README.md)):
```bash
python3 scripts/check_attempt_structure.py --offline --generate-list --output proofs/attempts/ATTEMPTS.md
```

New attempt folders should use the `original/ proof/ refutation/` layout
above. As of 2026-11-03, 56 of the 116 folders still use the older
`lean/ rocq/` layout.

> **Note:** Isabelle/HOL support has been sunset. Existing Isabelle proofs are archived in [`./archive/isabelle/`](archive/isabelle/) for reference. New formalizations should use Lean or Rocq.

### Lean 4 Guidelines

**No central file updates needed!** The `lakefile.lean` uses auto-discovery:
```lean
lean_lib «proofs» where
  globs := #[.submodules `proofs]
```

Simply add your `.lean` file in the appropriate directory and it will be automatically discovered.

**Common issues to avoid:**
- Do not use `ℕ` - use `Nat` instead (Mathlib is not configured)
- Mathlib is not configured; avoid Mathlib-only tactics such as `norm_num`. Core Lean tactics such as `omega`, `simp`, and `decide` are available without Mathlib.
- `#print "string"` is valid Lean 4 syntax; use `#print name` to inspect a declaration.
- Avoid reserved keywords as field names (e.g., `from`, `to`)

#### Core Lean example

Save this as `CoreTactics.lean` and run `lake env lean CoreTactics.lean` from the repository root:

```lean
example (n : Nat) : n ≤ n + 1 := by omega
example (n : Nat) : n + 0 = n := by simp
example : 2 + 2 = 4 := by decide
#print "supported"
```

See the [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) for the core tactics and their syntax.

### Rocq Guidelines

Add your `.v` file to the appropriate directory and list it in the root `_CoqProject` file. The Rocq build uses this file to compile imports before their users. Check that the list is complete with `python3 -m unittest experiments.issue611.test_rocq_project`.

### Code Quality

**For formalizations demonstrating failed proof attempts:**
- Reserve `sorry` (Lean) and `Admitted` (Rocq) for unresolved historical premises in a reconstructed proof attempt. State the exact missing proposition, explain the gap in a nearby comment, and track it in the attempt README. Do not use admissions for routine proof obligations that core tactics can solve.
- When a result depends on such a premise, prefer an explicit theorem parameter so the dependency remains visible.
- The goal is to demonstrate the error in the original proof attempt, not to complete an impossible proof
- State the exact proposition from the source that a named refutation disputes, including its input conditions. A counterexample must satisfy those conditions and compute the failed result.
- Label calculations on simplified models as illustrations or conditional results. A theorem ending in True, or a proof about arbitrary objects unrelated to the paper's construction, does not establish a refutation.
- In the attempt README and the common-errors index, distinguish a concrete refutation from a conditional result, an identified gap, and informal/unverified analysis.
- Keep false or unproved historical premises as explicit theorem parameters, not global axioms that allow unrelated imports to prove anything
- Do not describe a compiling attempt or refutation as certified. Only conclusions listed in `scripts/proof_status.json` receive the assumption audit

### CI Checks

The workflow in `.github/workflows/verification.yml` selects jobs by the
paths a change touches; it does not run every prover on every push. It
compiles Lean and Rocq proof files, and checks the Agda files listed in the
workflow. Historical compilation permits admissions and axioms. The separate
certified-result audit runs `scripts/check_proof_status.py` against the
conclusions in `scripts/proof_status.json` and fails on admissions or
unapproved assumptions.

The first job (`detect-changes`) runs on every push to `main` and every pull
request. As of 2026-11-03 the working-tree workflow (not yet pushed) adds
these steps to it:

- **Formal statement and hypothesis manifest:**
  `python3 -I scripts/test_check_formal_statement.py`, then
  `python3 -I scripts/check_formal_statement.py`.
- **Literature registry:** `python3 -I scripts/test_check_literature_registry.py`,
  then `python3 -I scripts/check_literature_registry.py` (validation) and
  `python3 -I scripts/check_literature_registry.py --check-render` (checks
  that `literature/REGISTRY.md` matches `literature/registry.json`).
- **Claims ledger:** `python3 -I scripts/test_check_claims.py`, then
  `python3 -I scripts/check_claims.py --run-scripts` (checks `CLAIMS.md`).

The commands are listed under [Checks to run](#checks-to-run).

Ensure the modules you changed compile locally before submitting.

### Commit Messages

Use clear, descriptive commit messages:
```
feat: Add [Author] [Year] P=[NP/P≠NP] formalization

- Add formalization in [Lean/Rocq]
- Identify error: [brief description of the error]
- Document the gap in the proof
```

### Pull Request Guidelines

1. Reference the related issue. Use "Refs #N" for a slice of a larger issue.
   Use "Fixes #N" only when the PR delivers the issue's whole deliverable.
   For the track issues #567 and #568 that means a closing theorem: a
   declaration whose type is exactly `Complexity.PNotEqualsNP` (#567) or
   `Complexity.PEqualsNP` (#568), with no arguments, certified in both
   provers, with its `#check` / `Check` output and an assumption report that
   lists only the allowed axioms pasted in the PR (see
   [ROADMAP.md](ROADMAP.md#definition-of-done), item 9). Every other PR on
   those issues says "Refs".
2. Describe the proof attempt being formalized
3. Explain the identified error or gap
4. Ensure all CI checks pass. Keep the PR in draft while CI is red.
5. Fill in the template under
   [Result classes and PR description template](#result-classes-and-pr-description-template).

## Adding results outside `proofs/attempts/`

New ideas and issue experiments live in `proofs/experiments/issueN/`, with
paired `lean/` and `rocq/` files.

- Import the shared model (`proofs/complexity/`) and, for SAT, `Machines`
  from `proofs/experiments/issue532/`. Do not define a second P, NP or SAT.
- Use the same theorem names in Lean and Rocq. Add Rocq files to
  `_CoqProject`.
- No admissions or axioms. State every unproved premise once as a
  proposition, pass it as a theorem argument, and register it in
  [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md). Classify it as a known
  theorem not yet mechanized or as an open obligation. An open obligation is
  at least as hard as an open problem: use it only in theorems that show what
  it would imply, never as a premise of a result reported as progress.
- Register conclusions you want certified in `scripts/proof_status.json` for
  both provers.
- Agda files are checked only if they are listed in
  `.github/workflows/verification.yml`.
- The legacy frameworks in `proofs/p_eq_np/` and
  `proofs/experiments/{lean,rocq}/PvsNPProofAttempt.*` still carry axioms
  (#627). Do not import them.

## Prior-art search (required before a new lemma)

Start from the precise local obligation: its name, statement and owning issue.
Then search in this order and stop as soon as a source settles the question:

1. Local declarations: `grep -rn` over `proofs/` for the name, key
   definitions and likely equivalent formulations.
2. The [research log](proofs/experiments/issue532/RESEARCH_LOG.md) and the
   dossiers in `proofs/experiments/issue532/ideas/`.
3. `proofs/attempts/` and [COMMON_ERRORS.md](proofs/attempts/COMMON_ERRORS.md).
4. [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md) and the open issues.
5. The literature registry: [literature/REGISTRY.md](literature/REGISTRY.md)
   and `literature/registry.json`.
6. Primary publications and external formal libraries.

Keep a short search log in the PR or the owning issue, with these fields:

| Field | Content |
| --- | --- |
| Obligation | local name and owning issue |
| Date | date of the search |
| Queries | the exact terms or statements searched |
| Registry revision | commit of `literature/registry.json` used |
| Hits | registry IDs or URLs, each with source revision and declaration |
| Decision | `reuse`, `adapt`, `reject` or `defer`, per hit |
| Reason | statement comparison; model, cost and encoding differences; trust and license status; remaining bridge |

Cite the original result rather than copying a large or uncleared artifact.
An empty search log is not permission to claim a new theorem; it records what
was checked. Absence from this repository does not make an idea new.

**Stopping rule.** Search with a fixed budget (for example 30 minutes or 20
results per step). If a proof stalls:

1. Isolate the smallest failing goal and its assumptions.
2. Search local names and the registry for it.
3. Search external sources within the budget.
4. Try one counterexample or simplification test.
5. Write a stopping note.
6. Post the named open obligation on the owning issue instead of retrying.

Reopen the search only after a new release, a changed formal target, or a new
citation. The search does not have to cover the whole Internet before every
edit.

## Result classes and PR description template

Every substantive PR states one result class, as defined in
[RESEARCH_VISION.md](RESEARCH_VISION.md#2-principles):

- known theorem mechanized;
- algorithm-specific refutation;
- restricted-model lower bound;
- conditional general result;
- unconditional general result.

It also states, separately, a provenance label. #568 (section 7) defines
four: known theorem newly mechanized, new-to-repository engineering, new
mathematical result, or conjecture. This repository adds a fifth, known
theorem reused, for a PR that only applies a result already mechanized here;
it is a repository extension, not part of #568. Attempt analyses keep the
evidence levels of COMMON_ERRORS.md.

```text
Result class:
Provenance:
Before / after: <statements; the premise removed or the scope proved>
Explicit hypotheses remaining: <names, each in proofs/HYPOTHESES.md>
Assumption reports: <#print axioms and Print Assumptions output>
Error families checked: <COMMON_ERRORS numbers, with evidence>
Mutation and non-vacuity tests: <what is rejected, and why>
Prior-art search log: <link>
Refs #N
```

Theorem counts, lines of code and passing CI runs are not results.

## Safety and reproducibility for external sources

- Papers, archives, repositories and generated proofs from outside are
  untrusted data. Do not run downloaded scripts, build files or model code
  outside an isolated environment. Read them with `python3 -I`.
- Do not expose secrets or tokens to search tools. Do not call external APIs
  unless the task requires it.
- Do not vendor material whose license is unknown. Link it and record it in
  the registry instead.
- Pin every external source to an immutable revision. Fetch single files with
  `gh api` or a sparse checkout. Do not clone multi-gigabyte repositories or
  run multi-hour builds on a development machine; use CI with a time and disk
  budget.
- A kernel check of an upstream proof is not a result of this repository.
  Follow the intake steps in
  [RESEARCH_VISION.md](RESEARCH_VISION.md#5-how-we-take-in-new-results):
  registry entry, fidelity audit, named bridge obligations, optional CI
  re-verification, dated notes.

## Checks to run

Toolchains: Lean `v4.34.1` (core Lean, no Mathlib), Rocq 9.0 in CI, Agda in a
pinned container (see [AGENTS.md](AGENTS.md)).

```sh
lake build                                   # or: lake build <module.name>
rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
python3 -m unittest experiments.issue611.test_rocq_project
python3 scripts/check_proof_status.py        # source scan of certified files
python3 scripts/check_proof_status.py --lean # after building; also --rocq
python3 -I scripts/check_formal_statement.py
python3 -I scripts/check_literature_registry.py
python3 -I scripts/check_claims.py --run-scripts
```

## Questions?

Open an issue if you have questions about contributing.
