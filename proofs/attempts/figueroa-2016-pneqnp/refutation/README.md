# Refutation: Why Figueroa's Proof Fails

This document explains the critical errors in Javier A. Arroyo-Figueroa's 2016 attempt to prove P ≠ NP.

For the original proof idea, see [`../README.md`](../README.md).

---

## Executive Summary

The Figueroa (2016) proof attempt **fails due to a critical function type mismatch**. The paper claims to construct functions mapping n-bit inputs to n-bit outputs, but the actual construction produces n²-bit outputs. This error invalidates all probability calculations and prevents the proof from establishing the existence of one-way functions.

---

## The Critical Error: Type Mismatch

### The Type Mismatch

**Claimed Function Type**: τ : {0,1}ⁿ → {0,1}ⁿ
- Input: n bits
- Output: n bits

**Actual Function Type**: τ : {0,1}ⁿ → {0,1}ⁿ²
- Input: n bits
- Output: n² bits

### Why This Happens

The construction process:
1. Takes an input of n bits
2. For each input bit, generates n output bits using hash functions and bit matrices
3. Concatenates all outputs
4. Results in n × n = n² total output bits

### Numerical Example

For n = 10:
- **Claimed**: 10-bit input → 10-bit output
- **Actual**: 10-bit input → 100-bit output (10x difference)

For n = 100:
- **Claimed**: 100-bit input → 100-bit output
- **Actual**: 100-bit input → 10,000-bit output (100x difference)

---

## Cascading Consequences

### 1. Incorrect Preimage Size

**Claimed Preimage Size**: 2ⁿ (for n = 10: 1,024 possible inputs)

**Actual Preimage Size**: 2ⁿ² (for n = 10: 2¹⁰⁰ ≈ 10³⁰ possible inputs)

**Error Factor**: 2ⁿ²⁻ⁿ = 2ⁿ⁽ⁿ⁻¹⁾

### 2. Wrong Probability Calculations

**Claimed Inversion Probability**: ~1/2ⁿ

**Actual Inversion Probability**: ~1/2ⁿ²

The actual probability is exponentially smaller than claimed, but this doesn't help the proof — it just means the analysis is completely wrong.

### 3. Invalid One-Way Function Claim

To prove a function is one-way, you need:
1. ✓ Polynomial-time computability (this part is fine)
2. ✗ Correct probability analysis (this is broken)

Without correct probability bounds, the one-wayness claim cannot be established.

### 4. Failed P≠NP Conclusion

The logical chain breaks:
1. ✗ τ functions are one-way (not proven due to type error)
2. ✗ One-way functions exist (not established)
3. ✗ P≠NP (does not follow)

---

## Additional Errors Identified by Juvekar, Narváez, and Welsh (2021)

### Ambiguous Hash Function Definitions

The construction of the universal hash functions is ambiguous, with unclear definitions of:
- The set of hash functions being used
- How these functions are selected
- The domain and codomain of these functions

This affects calculations of hash function preimages, probability of selecting specific inputs, and the entire probability analysis.

### Probability Argument Failure

The methodology for computing probabilities (dividing favorable outcomes by the size of the outcome space) doesn't establish the formal definition of one-wayness.

Even if the construction were well-defined, the proof doesn't demonstrate that the functions satisfy the cryptographic definition of one-way functions, which requires that for any probabilistic polynomial-time algorithm A, the probability that A(τ(x)) returns a preimage of τ(x) is negligible.

### Circular Reasoning

The construction assumes the existence of properties that would themselves imply P ≠ NP, without proving these properties hold for the constructed functions.

---

## Why Formal Verification Catches This

A formal proof system immediately rejects this proof because:

```rocq
(* Rocq would reject: *)
Definition tau : BitSeq -> BitSeq := fun input =>
  (* ... construction that produces n² bits ... *)

Axiom tau_type : forall input,
  bit_length input = n -> bit_length (tau input) = n.

(* Type error: cannot prove n = n² for n ≥ 2 *)
```

```lean
-- Lean would reject:
def tau : BitSeq → BitSeq := fun input =>
  -- ... construction that produces n² bits ...

theorem tau_type (input : BitSeq) (h : bitLength input = n) :
  bitLength (tau input) = n := by
  sorry -- Cannot be proven!
```

---

## Formalization Files

- [`lean/FigueroaAttempt.lean`](lean/FigueroaAttempt.lean) — Lean 4 formalization exposing the type error
- [`lean/Figueroa2016.lean`](lean/Figueroa2016.lean) — Alternative Lean 4 formalization
- [`rocq/FigueroaAttempt.v`](rocq/FigueroaAttempt.v) — Rocq formalization exposing the type error
- [`rocq/Figueroa2016.v`](rocq/Figueroa2016.v) — Alternative Rocq formalization

All formalizations:
- ✓ Model the construction
- ✓ Show actual output length is n²
- ✓ Prove the type mismatch
- ✓ Demonstrate the proof cannot go through

---

## References

1. Arroyo-Figueroa, J.A. (2016). "The Existence of the Tau One-Way Functions Class as a Proof that P != NP". arXiv:1604.03758.
2. Juvekar, M., Narváez, D.E., & Welsh, M. (2021). "On Arroyo-Figueroa's Proof that P ≠ NP". arXiv:2103.15246.
