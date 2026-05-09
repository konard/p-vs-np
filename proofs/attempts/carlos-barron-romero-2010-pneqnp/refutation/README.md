# Refutation Formalization

This directory contains the formal refutation of Carlos Barron-Romero's 2010 P≠NP
argument from arXiv:1006.2218v1.

## The Core Error

The paper commits a fundamental definitional error:

> **Barron-Romero's error**: Proposition 1.1 claims NP problems lack polynomial
> verification algorithms. This directly contradicts the definition of NP, which
> requires polynomial-time verification by definition.

## What We Prove

### 1. Proposition 1.1 Is False by Definition
```
theorem proposition1_1_false:
  ∀ prob, InNP prob → ¬ prop1_1 prob
```
Any NP problem has a polynomial verifier (by definition of NP), so Proposition 1.1
is false for every NP problem.

### 2. TSP Verification Is Polynomial
```
theorem tsp_verification_polynomial: PolynomialBound verificationTime
```
Given a proposed TSP tour, we can verify it in O(n) time:
1. Check the tour visits each city exactly once: O(n)
2. Compute the total cost: O(n)
3. Compare with the budget: O(1)

### 3. Algorithm 9 Is a Solver, Not a Verifier
```
theorem solving_vs_verifying:
  ¬ PolynomialBound algorithm9_iterations ∧ PolynomialBound verificationTime
```
Algorithm 9 (enumerate all (n-1)! tours) **solves** TSP by finding the optimal
tour. It does **not** verify a given proposed tour. The paper confuses these.

### 4. The Core Inference Is Invalid
```
theorem barronRomero_invalid_inference_is_false:
  ¬ barronRomero_invalid_inference
```
The inference "search is exponential → verification is exponential" is false.
Standard complexity theory explicitly distinguishes finding from verifying.

## Files

- `lean/BarronRomeroRefutation.lean` — Lean 4 formal refutation
- `rocq/BarronRomeroRefutation.v` — Rocq formal refutation

## Summary

| Claim | Truth | Formalization |
|-------|-------|---------------|
| TSP has (n-1)! possible tours | ✓ True | Proven |
| Algorithm 9 runs in (n-1)! time | ✓ True | Proven |
| Algorithm 9 is the only verifier | ✗ False | Refuted |
| TSP has no polynomial verifier | ✗ False | Refuted |
| P ≠ NP (from this argument) | ✗ Unproven | Invalid inference |

## See Also

- [Forward Proof](../proof/README.md) — The paper's argument structure
- [Main README](../README.md) — Overview and analysis
