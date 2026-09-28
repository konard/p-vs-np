# Contributor guide Lean example regression

Run `python3 experiments/issue585/check_guidance.py` from the repository root.
The check extracts the core Lean example from `CONTRIBUTING.md`, verifies that
it demonstrates `omega`, `simp`, `decide`, and `#print "supported"` without
`sorry`, then compiles it using the repository's Lean toolchain and no Mathlib.

Before the guide was corrected, the check failed because the buildable example
was absent. CI runs the check in the Lean job whenever the guide changes.
