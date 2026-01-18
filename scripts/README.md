# Scripts

This directory contains utility scripts for managing and tracking P vs NP proof attempts.

## check_attempts.py

A Python script that compares the repository's formalized attempts against [Woeginger's P vs NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) and checks the completeness of each formalization.

### Requirements Checked

Per the specifications in [Issue #44](https://github.com/konard/p-vs-np/issues/44), each formalization should have:

1. **README.md** - Detailed description of the attempt, including:
   - How the attempt was structured
   - The core idea
   - How it intended to solve P vs NP
   - Detailed explanation of the errors found

2. **Original Papers** - The original paper(s) or at minimum a README.md documenting the attempt

3. **Formalization** (Coq/Lean/Isabelle) - Full proof draft (formal version of the paper) with:
   - All parts that break apart commented
   - Explanations on why and how they break

4. **Formal Refutation** (Coq/Lean/Isabelle) - Not just showing errors in words, but proving the refutation formally

### Usage

```bash
# Basic report
python3 scripts/check_attempts.py

# JSON output (for CI integration)
python3 scripts/check_attempts.py --json

# Verbose output with details
python3 scripts/check_attempts.py --verbose

# Show only missing attempts
python3 scripts/check_attempts.py --missing-only

# Show only incomplete attempts
python3 scripts/check_attempts.py --incomplete-only
```

### Output

The script produces:

- **Summary Statistics** - Total counts for each component (README, papers, formalizations, refutations)
- **Missing Attempts** - Attempts from Woeginger's list not yet mapped to the repository
- **Incomplete Attempts** - Mapped attempts that need additional work
- **Unmapped Folders** - Repository folders not matching any attempt in Woeginger's list

### Completeness Score

Each attempt is scored 0-100% based on:
- Has folder: 10%
- Has README.md: 10%
- README has detailed description: 10%
- README has error explanation: 10%
- Has original paper: 10%
- Has Lean formalization: 10%
- Has Coq formalization: 10%
- Has Isabelle formalization: 10%
- Has formal refutation (in any prover): 20%

### Status Emoji Legend

- ✅ Complete (90-100%)
- 🟡 Nearly complete (70-89%)
- 🟠 In progress (50-69%)
- 🔴 Started (1-49%)
- ⬜ Not started (0%)

## Reference

Source list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
