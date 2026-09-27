# Contributing to P vs NP Research Repository

Thank you for your interest in contributing to this educational research repository!

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

To generate a markdown list of all attempts:
```bash
python3 scripts/check_attempt_structure.py --generate-list --output proofs/attempts/ATTEMPTS.md
```

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

Add your `.v` file to the appropriate directory. Update the local `_CoqProject` file if one exists.

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

The workflow compiles Lean and Rocq proof files, and checks the listed shared-model Agda files. Compilation permits admissions and axioms. The separate certified-result audit runs `scripts/check_proof_status.py` against the conclusions in `scripts/proof_status.json` and fails on admissions or unapproved assumptions.

- Lean compilation: `lake build`
- Rocq compilation: `rocq compile`
- Certified source check: `python3 scripts/check_proof_status.py`
- Certified assumption check after building: `python3 scripts/check_proof_status.py --lean` or `--rocq`

Ensure your code compiles locally before submitting.

### Commit Messages

Use clear, descriptive commit messages:
```
feat: Add [Author] [Year] P=[NP/P≠NP] formalization

- Add formalization in [Lean/Rocq]
- Identify error: [brief description of the error]
- Document the gap in the proof
```

### Pull Request Guidelines

1. Reference the related issue (e.g., "Fixes #123")
2. Describe the proof attempt being formalized
3. Explain the identified error or gap
4. Ensure all CI checks pass

## Questions?

Open an issue if you have questions about contributing.
