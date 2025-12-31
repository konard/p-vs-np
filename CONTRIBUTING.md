# Contributing to P vs NP Research Repository

Thank you for your interest in contributing to this educational research repository!

## Adding New Proof Attempt Formalizations

When adding a new formalization of a P vs NP proof attempt, follow these guidelines to minimize merge conflicts and ensure CI passes.

### Directory Structure

Create your formalization in:
```
proofs/attempts/<author-year-claim>/
├── README.md           # Description of the attempt and identified errors
├── lean/
│   └── YourTheory.lean
├── coq/
│   └── YourTheory.v
└── isabelle/
    ├── ROOT            # REQUIRED: Session configuration
    └── YourTheory.thy
```

### Lean 4 Guidelines

**No central file updates needed!** The `lakefile.lean` uses auto-discovery:
```lean
lean_lib «proofs» where
  globs := #[.submodules `proofs]
```

Simply add your `.lean` file in the appropriate directory and it will be automatically discovered.

**Common issues to avoid:**
- Do not use `ℕ` - use `Nat` instead (Mathlib is not configured)
- Do not use Mathlib tactics like `omega`, `norm_num`, `simp`, `decide` - use `sorry` for incomplete proofs
- Do not use `#print "string"` - this is not valid Lean 4 syntax
- Avoid reserved keywords as field names (e.g., `from`, `to`)

### Isabelle Guidelines

**No central ROOT file!** Each theory directory must have its own ROOT file.

Create a ROOT file in your `isabelle/` directory:
```
session "YourSessionName" = HOL +
  options [timeout = 300, quick_and_dirty]
  theories
    YourTheory
```

**If your theory requires additional libraries**, update the parent session:
- `HOL-Library` for `FSet`, `Multiset`, `FuncSet`, etc.
- `HOL-Analysis` for `Analysis`, `Probability`, etc.
- `HOL-Combinatorics` for combinatorics libraries

Example:
```
session "YourSessionName" = "HOL-Library" +
  options [timeout = 300, quick_and_dirty]
  theories
    YourTheory
```

### Coq Guidelines

Add your `.v` file to the appropriate directory. Update the local `_CoqProject` file if one exists.

### Code Quality

**For formalizations demonstrating failed proof attempts:**
- Using `sorry` (Lean), `Admitted` (Coq), or `oops` (Isabelle) is acceptable to mark where proofs cannot be completed
- Add clear comments explaining why the proof fails at that point
- The goal is to demonstrate the error in the original proof attempt, not to complete an impossible proof

### CI Checks

All proof files are verified by GitHub Actions:
- Lean: `lake build`
- Isabelle: `isabelle build -D .` (auto-discovers all ROOT files)
- Coq: Standard coqc compilation

Ensure your code compiles locally before submitting.

### Commit Messages

Use clear, descriptive commit messages:
```
feat: Add [Author] [Year] P=[NP/P≠NP] formalization

- Add formalization in [Lean/Coq/Isabelle]
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

