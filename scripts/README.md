# Scripts

This directory contains utility scripts for managing the P vs NP attempts repository.

## check_attempt_structure.py

A script to verify that P vs NP attempts follow the required directory structure.

### Required Structure

Each attempt should follow this structure:

```
attempt-name/
├── README.md              # Overview of the attempt
├── original/              # Description of the proof idea
│   ├── README.md         # Detailed description of the approach
│   └── paper/            # Optional: references to original papers
├── proof/                 # The forward proof formalization
│   ├── lean/             # Lean 4 formalization (*.lean)
│   └── rocq/             # Rocq formalization (*.v)
└── refutation/           # The refutation formalization
    ├── README.md         # Explanation of why the proof fails
    ├── lean/             # Lean 4 refutation (*.lean)
    └── rocq/             # Rocq refutation (*.v)
```

### Directory Descriptions

- **original/**: Contains the description of the original proof idea
  - What the author claimed
  - The approach they used
  - Historical context

- **proof/**: Contains formalizations of the proof STRUCTURE (not claiming it's correct)
  - Shows how the proof would work IF its axioms were true
  - Helps understand the logical structure
  - Must have at least Lean or Rocq formalization

- **refutation/**: Contains formalizations demonstrating WHY the proof fails
  - Shows where the proof breaks down
  - Formalizes counterexamples or logical gaps
  - Must have at least Lean or Rocq formalization

### Usage

```bash
# Check all attempts
python3 scripts/check_attempt_structure.py

# Check a specific attempt
python3 scripts/check_attempt_structure.py --path proofs/attempts/craig-feinstein-2003-pneqnp

# Specify a different base directory
python3 scripts/check_attempt_structure.py --base-dir /path/to/repo
```

### Output

The script produces a report showing:
- Total attempts scanned
- Complete attempts (following new structure)
- Incomplete/legacy attempts (missing required components)
- Warnings (e.g., deprecated directories)

### Legacy Structure Detection

The script also detects legacy structure patterns:
- `coq/` directory at root level (should be `proof/rocq/` and `refutation/rocq/`)
- `lean/` directory at root level (should be `proof/lean/` and `refutation/lean/`)
- `isabelle/` directory (Isabelle support has been sunset)

### Notes

- Isabelle support has been sunset. Existing Isabelle files should be archived, not included in new attempts.
- At least one of Lean or Rocq formalization is required in both `proof/` and `refutation/`.
- The `paper/` subdirectory in `original/` is optional but recommended.

## Future Scripts

Additional scripts may be added to:
- Validate formalization syntax
- Generate attempt templates
- Cross-reference with Woeginger's list
- Produce coverage statistics
