# Polynomial-bound regression (issue #574)

`PolynomialRegression.lean` and `PolynomialRegression.v` check the shared
`c * (n + 1) ^ k` bound at input length zero and for constant, linear, summed,
multiplied, and composed functions. They also check a local proof-attempt alias
in each language. Before this change, the first Lean example failed with
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
