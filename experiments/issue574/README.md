# Polynomial-bound regression (issue #574)

Status at 2026-11-03: a passing regression for issue #574 (closed). CI
compiles `PolynomialRegression.lean` in the Lean job and the three `.v` files through
`_CoqProject` in the Rocq job.

`PolynomialRegression.lean` and `PolynomialRegression.v` check the shared
`c * (n + 1) ^ k` bound at input length zero and for constant, linear, summed,
multiplied, and composed functions. They also check a local proof-attempt alias
in each language. That alias comes from the legacy `PvsNPProofAttempt` files,
which carry axioms, are not certified, and are slated for archiving in
[#627](https://github.com/konard/p-vs-np/issues/627). Before this change, the first Lean example failed with
`⊢ n + 1 ≤ n` after choosing `c = k = 1`; the former exponent-only predicate
also rejected the constant `42` at `n = 1`.

Run the regressions after building the imported modules:

```sh
lake build
lake env lean experiments/issue574/PolynomialRegression.lean
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/rocq/PvsNPProofAttempt.v
rocq compile -Q . '' experiments/issue574/PolynomialRegression.v
```

The `CheckLemmas` and `CheckShared` files record the small library checks used
while constructing the closure proofs.
