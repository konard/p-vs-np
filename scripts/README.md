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

## check_issue624_completion.py

PR #630 requires the complete Cook–Levin construction, rather than only the
entries currently registered in `proof_status.json`. This additional gate
requires 29 paired public contracts: the complete tableau's model extraction
and representation, satisfiability equivalence, polynomial bit length under
the shared unary `encodeCNF`, a charged `Computes` proof for one reduction
machine fixed for all inputs, `satHard`, `cookLevin`, three negative results,
and the specified machine-model bridges without SAT-hardness premises.

The gate expects the construction to export `Issue624.CookLevin` in Lean and
`CookLevin` in Rocq. Its actual defining files are selected by the certified manifest; the
gate does not require all the implementation in one file. The exact expected
types are maintained as paired contracts in the script. Representation and
extraction use the existing `WindowVerifierTableau`, which reuses #568's
`LocalTrace` and the certificate-dependent clock recovery proof.
Shared model references are fully qualified so exported names cannot shadow
the predicates being checked. Construction contracts quantify explicitly over
the entire shared `ClassNP` and `Word` types.

```bash
python3 -m unittest experiments.issue624.test_completion experiments.issue624.test_completion_workflow -v
python3 scripts/check_issue624_completion.py          # source/manifest preflight
python3 scripts/check_issue624_completion.py --lean   # after building Lean
python3 scripts/check_issue624_completion.py --rocq   # after building Rocq
bash experiments/issue624/check.sh completion         # full local completion gate
```

The preflight reports missing registrations and remaining hardness arguments
with source line numbers. Passing the preflight alone does not certify
completion. Both kernels must accept each **unapplied** declaration at its
required type; this rejects explicit, implicit, and aliased extra premises.
The shared assumption checker audits their import closures and transitive
assumptions. The completion allowlist cannot be expanded beyond `propext`,
`Classical.choice`, `Quot.sound` (Lean), or `Classical_Prop.classic` (Rocq).
Idea 36's separate `VCHard` and vertex-cover obligations are preserved; it
has no `SATHard` or `CookLevin` argument to remove.

`Issue 624 Completion` runs independently of change detection on every PR
#630 update (including documentation-only changes) and manual runs of its
prepared branch. It fails while any endpoint contract is absent. It preserves
diagnostic logs as a workflow artifact. `Verification Summary` requires this
job to succeed on that PR, rejecting skipped and cancelled states as well as
failures. Unrelated PRs retain the existing verification selection. On GitHub,
`main` requires the GitHub Actions `Verification Summary` check, with strict
up-to-date checking and administrator enforcement enabled.

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
