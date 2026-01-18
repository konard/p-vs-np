# Scripts

This directory contains utility scripts for managing the P vs NP attempts repository.

## check_attempts.py

A comprehensive verification script that checks all P vs NP attempts against Woeginger's authoritative list.

### Purpose

This script helps maintain the quality and completeness of the repository by:

1. **Comparing against Woeginger's list**: Ensures we haven't missed any documented P vs NP attempts
2. **Verifying structure**: Checks that each attempt follows the expected pattern
3. **Identifying gaps**: Reports missing or incomplete formalizations
4. **Generating reports**: Produces both human-readable and JSON reports

### Expected Structure Pattern

Each attempt in `proofs/attempts/` should follow this structure:

```
proofs/attempts/<author>-<year>-<claim>/
├── README.md                    # REQUIRED: Detailed description
├── papers/                      # Optional: Original papers (PDF)
├── lean/                        # At least one formalization required
│   ├── <AttemptName>.lean      # Main formalization
│   └── <AttemptName>Refutation.lean  # Optional: Formal refutation
├── coq/                         # Optional alternative formalization
│   ├── <AttemptName>.v
│   └── <AttemptName>Refutation.v
└── isabelle/                    # Optional alternative formalization
    ├── <AttemptName>.thy
    └── <AttemptName>Refutation.thy
```

### Naming Convention

Directory names follow this pattern:
- `<author>-<year>-<claim>`
- Author names are normalized (lowercase, spaces replaced with hyphens)
- Claim is either `peqnp` (for P=NP) or `pneqnp` (for P≠NP)

Examples:
- `moustapha-diaby-2004-peqnp`
- `lev-gordeev-2005-pneqnp`
- `mathias-hauptmann-2016-pneqnp`

### README.md Requirements

Each attempt's README.md should contain:

1. **Header Section**:
   - Attempt ID (from Woeginger's list)
   - Author name(s)
   - Year
   - Claim (P=NP, P≠NP, etc.)
   - Status (Refuted, Unresolved, etc.)

2. **Summary**: Brief overview of the attempt

3. **Main Argument**:
   - The core idea
   - The approach taken
   - Key technical claims

4. **The Error** (if refuted):
   - Fundamental flaw(s) in the argument
   - Why the error matters
   - Counter-examples (if applicable)

5. **Broader Context**:
   - Why this approach is tempting
   - Common misconceptions
   - Related work

6. **Formalization Goals**:
   - What is being formalized
   - What the formalization demonstrates
   - Limitations

7. **References**:
   - Original papers
   - Refutations
   - Related discussions

### Formalization Requirements

At least ONE of Lean/Coq/Isabelle formalization must be present.

Each formalization should include:

1. **Basic Definitions**: Formal definitions of key concepts
2. **Attempt Formalization**: The proof attempt formalized as code
3. **Comments**: Extensive comments explaining:
   - What each part does
   - Where the proof breaks down
   - Why it breaks down
4. **Refutation** (optional but encouraged): Formal proof showing where the error occurs

### Usage

Run the script from the repository root:

```bash
# Basic usage
python3 scripts/check_attempts.py

# Save JSON report
python3 scripts/check_attempts.py --json attempts_report.json

# Specify different base directory
python3 scripts/check_attempts.py --base-dir /path/to/repo
```

### Output

The script generates a report with:

1. **Summary Statistics**:
   - Total attempts in Woeginger's list
   - Total attempts in repository
   - Matched, complete, and incomplete attempts

2. **Missing Attempts**: Attempts from Woeginger's list not yet in the repository

3. **Incomplete Attempts**: Attempts missing required files (README.md or formalizations)

4. **Unmatched Directories**: Directories in the repo not matched to Woeginger's list

5. **Statistics by Claim Type**: Breakdown by P=NP, P≠NP, etc.

### Example Output

```
================================================================================
P vs NP ATTEMPTS - COMPLETENESS REPORT
================================================================================

SUMMARY
--------------------------------------------------------------------------------
Total attempts in Woeginger's list: 120
Total attempts in repository:      70
Matched attempts:                   68
Complete formalizations:            45
Incomplete formalizations:          23
Missing from repository:            52
Unmatched directories:              2

MISSING ATTEMPTS (Not in repository)
--------------------------------------------------------------------------------
  [1] Ted Swart (1986) - P=NP
      Linear programming formulations for Hamiltonian cycle
      Expected directory: ted-swart-1986-peqnp

...
```

### Integration with Development Workflow

This script should be run:

1. **Before creating new issues**: To identify what work needs to be done
2. **After adding new attempts**: To verify structure is correct
3. **Periodically**: To ensure completeness as Woeginger's list updates
4. **In CI/CD**: To automatically verify repository quality (future enhancement)

### Woeginger's List

The script includes a snapshot of Woeginger's list as of January 2026. The authoritative list is maintained at:
- https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

To update the list in the script:
1. Visit Woeginger's page
2. Update the `WOEGINGER_ATTEMPTS` list in `check_attempts.py`
3. Run the script to generate an updated report

### Future Enhancements

Potential improvements:
- Fetch Woeginger's list automatically from the web
- Check README.md content quality (not just existence)
- Verify formalization syntax (run Lean/Coq/Isabelle checks)
- Generate GitHub issues automatically for missing work
- Track refutation status more precisely
- Add paper verification (check if papers exist and are accessible)
