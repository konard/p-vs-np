# Scripts

This directory contains utility scripts for managing the P vs NP attempts repository.

## check_proof_status.py

`proof_status.json` is the explicit list of certified Lean and Rocq conclusions.
The rest of the attempt catalog is historical material. The checker scans each
certified source and its repository imports for admissions or unproved
declarations. After the listed modules are compiled, it queries each prover
with `#print axioms` or `Print Assumptions` and fails if a theorem has any
assumption outside its manifest allowance.

The issue #532 dossier gate separately scans every Lean and Rocq proof file in
that experiment and all its local imports. The certified manifest also queries
the public SAT membership theorem and its machine-model bridges. A premise
such as `SATHard` is a theorem parameter; it is not added to the allowed
global axioms. Historical attempt sketches outside these import closures keep
their admitted status.

```bash
python3 -m unittest scripts.test_check_proof_status -v
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The workflow runs historical compilation and certified audits as separate
jobs. Passing historical compilation does not change an attempt's status.

## list_issues.py

`list_issues.py` prints the repository's GitHub issues, excluding pull requests.
It needs only Python 3 and network access to the GitHub REST API. The issues
endpoint returns issues and pull requests together, so the script follows every
`Link: rel="next"` page before it filters out pull requests. By default the
listing is complete: all open and all closed issues, newest first. `--limit N`
lists only the N most recently created issues, and the header then says the
listing is partial.

```bash
python3 -m unittest scripts.test_list_issues -v
python3 scripts/list_issues.py
python3 scripts/list_issues.py --state open
python3 scripts/list_issues.py --repo OWNER/NAME --limit 50
```

Unauthenticated requests share GitHub's low per-IP rate limit. When `GH_TOKEN` or
`GITHUB_TOKEN` is set, it is sent as a bearer token and never printed; for
example, `GH_TOKEN="$(gh auth token)" python3 scripts/list_issues.py`.
Pagination links to another host are refused, so the token is only sent to
`--api-url`.

Exit status 0 means the listing was fetched and validated. Exit status 1 means a
transport failure, HTTP error (including rate limits), invalid JSON, or a
response that does not match the expected issue schema; nothing is printed on
stdout in that case, so an unavailable response is never shown as an empty
listing. Exit status 2 means invalid arguments. The tests serve canned API
responses from a local HTTP server and need no network access or credentials.

## check_attempt_structure.py

`check_attempt_structure.py` verifies that each attempt in `proofs/attempts/`
uses the current directory layout and, by default, compares the repository
against Gerhard Woeginger's live P-versus-NP milestones page.

### Required Structure

Each attempt should follow this structure:

```text
attempt-name/
├── README.md              # Overview of the attempt
├── original/              # Original proof idea and source material
│   ├── README.md          # Detailed description of the approach
│   ├── ORIGINAL.md        # Markdown reconstruction of the paper
│   ├── ORIGINAL.pdf       # Original paper file (or .html/.tex)
│   └── paper/             # Optional: references to original papers
├── proof/                 # Forward proof formalization
│   ├── README.md          # Explanation of the proof structure
│   ├── lean/              # Lean 4 formalization (*.lean)
│   └── rocq/              # Rocq formalization (*.v)
└── refutation/            # Refutation formalization
    ├── README.md          # Explanation of why the proof fails
    ├── lean/              # Lean 4 refutation (*.lean)
    └── rocq/              # Rocq refutation (*.v)
```

The checker still accepts legacy root-level `ORIGINAL.*` files for older
attempts, but `original/` is the preferred location for new work.
An attempt is reported as complete when it has the main README, original
markdown and source material, and both `proof/` and `refutation/` sections.
Each section must have a README and at least one Lean (`*.lean`) or Rocq
(`*.v`) file. An attempt with only the main README remains valid, but partial.
Legacy root-level `lean/*.lean` and `rocq/*.v` files count toward formalization
coverage in reports and `ATTEMPTS.md`. The checker warns about those layouts,
including when they coexist with `proof/` or `refutation/`. Root-level files do
not satisfy the recommended section requirements for completeness.

### Woeginger Coverage

For full repository scans, the checker fetches:

```text
https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
```

It parses the live milestone list, matches entries to local attempt directories
using author, year, claim, title, directory name, and README metadata, then
reports missing live entries and unmatched local directories. Missing live
entries should be tracked with GitHub issues before the PR is finalized.

Use `--offline` when a deterministic local-only structure check is needed.

### Usage

```bash
# Check structure and compare with Woeginger's live list
python3 scripts/check_attempt_structure.py

# Check structure without network access
python3 scripts/check_attempt_structure.py --offline

# Save a machine-readable report
python3 scripts/check_attempt_structure.py --json attempts_report.json

# Fail if any live Woeginger entry does not match a repository attempt
python3 scripts/check_attempt_structure.py --fail-on-missing-woeginger

# Check a specific attempt directory
python3 scripts/check_attempt_structure.py --path proofs/attempts/craig-feinstein-2003-pneqnp

# Generate the repository attempt index
python3 scripts/check_attempt_structure.py --offline --generate-list --output proofs/attempts/ATTEMPTS.md
```

`--fail-on-missing-woeginger` requires a successfully fetched and parsed
milestone list, including when `--quiet` is set. It can also use a local HTML
file through `--woeginger-url file:///absolute/path/to/snapshot.html`.
`--offline` and `--path` cannot be combined with strict Woeginger flags because
those modes skip the list comparison. Exit status 1 means that repository
coverage is incomplete (or an attempt is structurally invalid); exit status 2
means that the source could not be validated or the flags are incompatible.

### Output

The script reports:

- Total attempts scanned
- Complete attempts with original material, proof formalization, and refutation
- Partial or invalid attempts that need structure work
- Legacy layout warnings, including old root-level `lean/`, `coq/`, or `isabelle/`
- Live Woeginger entries that are missing from `proofs/attempts/`
- Repository attempts that do not match Woeginger's list

### Notes

- Isabelle support has been sunset. Existing Isabelle files should be archived,
  not included in new attempts.
- New attempts should include both `proof/` and `refutation/` directories.
- At least one of Lean or Rocq is expected in each formalization directory.
- The `original/paper/` subdirectory is optional and can hold supporting source
  references.

## check_formal_statement.py

Checks [FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md) and
[proofs/HYPOTHESES.md](../proofs/HYPOTHESES.md) against the Lean, Rocq and
Agda sources and [proof_status.json](proof_status.json). It uses only the
standard library and reads source text; it builds nothing, so a premise is
recognised by its name in the signature text, not by elaboration. Files
under `proofs/attempts/` are not scanned. CI runs it with its tests in the
`detect-changes` job of `.github/workflows/verification.yml` (added
2026-11-03, not yet pushed).

It fails (exit 1) if:

- a `path::Name` line of the `claims` block names a missing file or a name
  that the file does not declare;
- a location written as `` `Name` (`path:line`) `` (a `;` or `,` may follow
  the line number), a table cell `` `Name` `` followed by a cell
  `` `path:line` ``, or a lean or rocq cell of the hypotheses table does not
  declare the name on that line. A declaration at most three lines away is
  only a warning;
- **summary box** (the fenced block after `<!-- verbatim-from: path -->`): a
  code line does not occur in the source, or the code lines do not occur in
  the same order (contiguity is not required). A comment line
  `-- [path]:N` or `-- [path]:N-M` starts a group; the group's first code
  line must be source line N and its last line M. Groups must follow source
  order. Other `--` comment lines are ignored;
- **result graph** (the table with columns `edge (from → to) | theorem |
  file:line | premise | certified | status`): a name in the premise cell is
  not a premise of the theorem's signature, or a hypothesis (a row name of
  HYPOTHESES.md) is a premise but is neither in the premise cell nor in the
  edge cell; or `certified` is not `yes` exactly when `proof_status.json`
  lists the theorem for that source file. A premise is a bracketed binder
  before the top-level colon, a `∀`/`forall` binder, or the left side of a
  top-level arrow; the conclusion, an `↔` statement and the body of `∃` are
  not premises;
- **wording**: a prose sentence of either document that locates a theorem
  or lemma and calls it "certified", or "proved"/"proves" without "not
  certified", while `proof_status.json` does not list it;
- **hypotheses table**: other columns, classes or status values than the
  fixed ones; a lean or rocq cell that is not a `file:line` (or "not
  defined" in both cells, for a known theorem without a definition yet; such
  a name must not be defined as a Prop under `proofs/`); a row whose name is
  not declared as a Prop definition at that location (`def`, `abbrev`,
  `structure`, `class`, `inductive`, `opaque` … `: Prop` in Lean;
  `Definition`, `Record`, `Structure`, `Class`, `Inductive`, `Variant` …
  `: Prop` in Rocq); a statement cell that starts with a code span naming an
  identifier absent from the Lean definition; a class that disagrees with the
  marker of the Lean definition ("Open obligation" means `obligation`, a
  "Known theorem"/"not mechanised" marker alone means not `obligation`);
- **dependents**: a listed theorem that is not a Lean theorem whose
  signature takes the hypothesis as a premise; a list without "…" that omits
  such a theorem; a list with "…" that lacks "(N total)" or whose N is not
  the number of such theorems; "none" when there is one;
- **markers**: a Prop definition under `proofs/` (`.lean`, `.v`, `.agda`)
  whose own comment says "Known theorem", "not mechanised"/"not mechanized"
  or "Open obligation" (case-sensitive) has no row. The own comment is the
  comment just above the declaration; any number of blank lines and
  attributes may come between, but nothing else. An Agda definition needs a
  row with the same name. The "Missing markers" bullet of the Known defects
  section must name exactly the rows whose Lean definition has no marker,
  and each of them must have a row;
- **discharged on main**: a row with that status whose name is still a
  premise of a Lean or Rocq theorem, unless its dependents cell lists the
  theorems and a Known defects bullet that says "discharged" names it. In
  that case it is a warning.

`--strict` turns every warning (line drift, a documented discharged
hypothesis that is still a premise) into a failure. On `main` today
`--strict` fails because of `SATInNP`, which is proved but still a premise
of 23 Lean and 23 Rocq theorems.

Not checked: whether a class is right among `bridge`, `P-membership`,
`simulation` and `deep`; whether a statement cell is faithful beyond its
leading code span; reference cells; a premise hidden behind another
definition; an unmarked hypothesis that is neither in the table nor in the
Missing markers list; and any other prose (PR states, counts, dates).

A named hypothesis is a theorem argument, not an axiom, so
`check_proof_status.py` cannot see it. This script is the check for it.

```bash
python3 -I scripts/check_formal_statement.py
python3 -I scripts/check_formal_statement.py --write-lines   # refresh line numbers, then check
python3 -I scripts/check_formal_statement.py --strict        # warnings fail too
python3 -m unittest scripts.test_check_formal_statement -v
python3 -I -m unittest discover -s scripts -p 'test_check_formal_statement.py' -v
```

`--write-lines` also rewrites the line numbers in the summary box comments.
Under `python3 -I` the current directory is not on `sys.path`, so the
package form `scripts.test_check_formal_statement` does not import; use the
`discover` form instead.

## check_literature_registry.py

Validates [literature/registry.json](../literature/registry.json), queries it,
and renders [literature/REGISTRY.md](../literature/REGISTRY.md). Standard
library only. Validation fails (exit 1) if:

- an entry lacks a required field, or a controlled field (`artifact_class`,
  `result_type`, `status`, `claim_status_local`, `verified`, `tags`) has a
  value outside the fixed vocabulary;
- two entries share an `id`, a canonical URL, an `attempt_slug` or a
  `source_row`. arXiv URLs (abs or pdf, any version, `.pdf`, http or https,
  `www.` or `export.`) and doi.org URLs reduce to one paper key, which may
  appear in only one entry unless the two entries are linked by `parent`, and
  only once within an entry;
- `date` does not start with `year`, `date` is later than `added`, or `added`
  is later than the registry's `updated`;
- `claim_status_local` is `upstream-checked`, `locally-replayed`,
  `conditional-bridge` or `locally-certified` without a `formal` object whose
  `model`, `declaration`, `file` and `revision` are recorded (not empty,
  `n/a`, `none`, `unknown…`, `not applicable…` or containing `not recorded`);
- `claim_status_local` is `locally-certified` without a `local_certificate`
  equal to a `theorem` in `scripts/proof_status.json`. No entry has that value
  yet;
- `status` is `formally-checked`, or `result_type` is `ai-lab-lean-checked`,
  without a `formal` object;
- `status` is `peer-reviewed` but no `;`-separated part of `venue` is a
  publication venue rather than a preprint server or repository (arXiv, ECCC,
  Zenodo, HAL, Preprints.org, GitHub, an author's page and similar), or
  `result_type` is `peer-reviewed-theorem` without status `peer-reviewed`;
- `status` is `withdrawn`, `refuted`, `formally-checked` or
  `under-expert-review` with neither `documented_responses` nor `notes` that
  cite the source (a URL, an arXiv id, a DOI, a commit hash or a README);
- `claim_direction` disagrees with the `peqnp` and `pneqnp` tags: `peqnp`
  needs `peqnp` or `both`, `pneqnp` needs `pneqnp` or `both`, both tags need
  `both`, and `both` needs both tags;
- a `claimed-p-vs-np-proof` entry lacks the `claimed-proof` tag,
  `attempt_slug`, `claim_direction` or `common_errors_family`, or has a
  `claim_status_local` other than `discovered`, `statement-only` or
  `candidate`;
- the documentation disagrees with the registry (also `--check-readme`; skip
  with `--readme none`): [literature/README.md](../literature/README.md) is
  missing, its tag table differs from `TAGS`, its "Known gaps" bullet
  "Entries with `verified: no`" does not list exactly the `verified: no`
  entries, or a backticked kebab-case token with a year segment in that guide
  or in [CLAIMED_PROOFS_2017_2026.md](../literature/CLAIMED_PROOFS_2017_2026.md)
  (`--claimed`) is not a registry id, an `attempt_slug` or a
  `proofs/attempts/` folder.

A registry entry never certifies a result by itself. The validator checks
shape and vocabulary, not the truth of `status`; a reviewer still has to open
the source.

```bash
python3 -I scripts/check_literature_registry.py                    # validate
python3 -I scripts/check_literature_registry.py --stats            # counts by type, status, year
python3 -I scripts/check_literature_registry.py --tag eth          # query; also --type, --status, --text, --since, --json
python3 -I scripts/check_literature_registry.py --render           # rewrite literature/REGISTRY.md
python3 -I scripts/check_literature_registry.py --check-render     # fail if REGISTRY.md is stale (CI)
python3 -I scripts/check_literature_registry.py --check-readme     # guide and backlog against the registry
python3 -I scripts/test_check_literature_registry.py
```

After editing the registry, run `--render` and commit the regenerated
`REGISTRY.md` together with `registry.json`.

## check_claims.py

Checks the claims ledger [CLAIMS.md](../CLAIMS.md): the statements listed
there, each with the check behind it. The ledger is a curated list; a
statement that is not a row is not checked. Standard library
only; runs under `python3 -I`; no Lean or Rocq build. It fails (exit 1) if:

- an id is duplicated or not kebab-case, or a check type or status is outside
  the fixed vocabulary, or the status does not fit the check type;
- a `formal` row names a theorem that is not declared in its file or not
  listed in `scripts/proof_status.json`, lacks a Lean or a Rocq name, or takes
  a hypothesis of `proofs/HYPOTHESES.md` as an argument;
- a `formal-conditional` row names a premise that is not a row of
  `proofs/HYPOTHESES.md`, does not occur in the theorem's signature, or is
  not named in the claim text; or its Lean file is not under `proofs/`, or
  its Rocq file is not listed in `_CoqProject`;
- an `external-formal` or `source` row names an id missing from
  `literature/registry.json`, or a `cited` row's entry is neither
  `peer-reviewed` nor `formally-checked`;
- a `script` row's command is not a file under `scripts/` or `experiments/`,
  the claim text does not contain the `expect=` value, or, with
  `--run-scripts`, the command's output differs from it;
- a `to-formalize` row has no queue entry, or names a theorem that is already
  certified; a queue entry is duplicated, is not a `to-formalize` row, or
  lacks one of the fields Statement, Definitions, Hypotheses, Size, Result
  class and Provenance;
- an id in the list of claims that cannot be formalized is not a ledger row,
  or its check is not `source`, `unverified` or `external-formal`;
- a "stated in" file does not exist.

```bash
python3 -I scripts/check_claims.py                 # static checks
python3 -I scripts/check_claims.py --run-scripts   # also recompute every count (CI)
python3 -I scripts/check_claims.py --stats         # rows by status and check type
python3 -I scripts/check_claims.py --count certified-lean
python3 -I scripts/test_check_claims.py
```

The checker reads source text. A `checked-conditional` row shows that the
premise is an explicit argument, not that the file compiles; compilation
and axiom audits are the Lean and Rocq CI jobs.
