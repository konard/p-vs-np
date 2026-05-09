# Scripts

This directory contains utility scripts for managing the P vs NP attempts repository.

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
