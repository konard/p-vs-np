# Figueroa (2016) - P≠NP Proof Attempt

**Attempt ID**: 109
**Author**: Javier A. Arroyo-Figueroa
**Year**: 2016
**Claim**: P ≠ NP
**Status**: Refuted

## Source

- **ArXiv**: [1604.03758](https://arxiv.org/abs/1604.03758) - "The Existence of the Tau One-Way Functions Class as a Proof that P != NP"
- **Woeginger's List**: Entry #114 (previously #109)
- **Critique**: [arXiv:2103.15246](https://arxiv.org/abs/2103.15246) - "On Arroyo-Figueroa's Proof that P ≠ NP" by Mandar Juvekar, David E. Narváez, and Melissa Welsh (2021)

## Summary

In April 2016, Javier A. Arroyo-Figueroa published a paper claiming to prove P ≠ NP by establishing the existence of a special class of one-way functions called "Tau" (τ). The approach relies on the well-known result that the existence of one-way functions implies P ≠ NP.

## Main Argument

Arroyo-Figueroa's proof strategy consists of the following steps:

1. **Define a class of functions τ (Tau)** that map bit sequences to bit sequences
2. **Construct each τ function** using:
   - A collection of independent universal hash functions
   - These hash functions produce a starting coordinate
   - They define a path within a sequence of unique random bit matrices
3. **Prove these functions are one-way** by showing:
   - (i) Each τ function is computable in polynomial time
   - (ii) Any polynomial-time probabilistic algorithm has negligible probability of finding the inverse
4. **Conclude P ≠ NP** from the existence of one-way functions

The key claim is that "no polynomial-time algorithm exists to compute the inverse of members of Tau" and that "the inverse computation problem cannot be reduced to FSAT in polynomial time."

## Known Errors and Refutation

The proof was critiqued by Juvekar, Narváez, and Welsh (2021), who identified several fundamental errors:

### 1. Function Mapping Inconsistency

**Error**: The functions τ are defined as mapping bit sequences of length n to bit sequences of length n (τ: {0,1}ⁿ → {0,1}ⁿ), but the actual algorithm appends n bits for every input bit.

**Implication**: The functions should actually be defined as τ: {0,1}ⁿ → {0,1}^(n²), not τ: {0,1}ⁿ → {0,1}ⁿ. This inconsistency undermines the entire construction.

**Formalization Challenge**: This type error can be caught immediately in a formal proof system through type checking.

### 2. Ambiguous Hash Function Definitions

**Error**: The construction of the universal hash functions is ambiguous, with unclear definitions of:
- The set of hash functions being used
- How these functions are selected
- The domain and codomain of these functions

**Implication**: The ambiguity affects:
- Calculations of hash function preimages
- Probability of randomly selecting specific inputs
- The entire probability analysis used to argue "negligible" inverse-finding probability

**Formalization Challenge**: Attempting to formalize the construction forces precise specification of all components, immediately revealing these ambiguities.

### 3. Probability Argument Failure

**Error**: The methodology for computing probabilities (dividing favorable outcomes by the size of the outcome space) doesn't establish the formal definition of one-wayness.

**Implication**: Even if the construction were well-defined, the proof doesn't actually demonstrate that the functions satisfy the cryptographic definition of one-way functions, which requires that for any probabilistic polynomial-time algorithm A, the probability that A(τ(x)) returns a preimage of τ(x) is negligible.

**Formalization Challenge**: The gap between informal probability arguments and the precise definition of one-way functions becomes apparent when formalizing.

### 4. Circular Reasoning

**Implicit Error**: The construction assumes the existence of properties that would themselves imply P ≠ NP, without proving these properties hold for the constructed functions.

**Formalization Challenge**: Dependency tracking in formal proofs reveals circular assumptions.

## Why This Approach Cannot Work

The fundamental issue is that **proving the existence of one-way functions is believed to be as hard as proving P ≠ NP itself**. Any proof of one-way function existence must:

1. Construct an explicit function family
2. Prove it's computable in polynomial time (relatively easy)
3. Prove that NO polynomial-time algorithm can invert it (extremely hard)

Step 3 requires proving a strong lower bound on the computational complexity of inverting the function, which faces the same barriers as proving P ≠ NP directly:
- Relativization barrier
- Natural proofs barrier
- Algebrization barrier

Arroyo-Figueroa's approach doesn't address these barriers and uses informal probabilistic arguments that don't constitute a rigorous complexity-theoretic lower bound.

## Formalization Goals

This directory contains formalizations in Coq, Lean, and Isabelle that attempt to:

1. **Define the basic concepts**:
   - Universal hash functions
   - One-way functions (cryptographic definition)
   - Polynomial-time computability
   - Negligible probability

2. **Formalize Arroyo-Figueroa's construction** (as much as possible given the ambiguities):
   - The τ function family
   - The hash function composition
   - The bit matrix path construction

3. **Identify where the proof breaks down**:
   - Type errors in function signatures
   - Missing or ambiguous definitions
   - Gaps in the one-wayness proof
   - Invalid probability arguments

4. **Document lessons learned**:
   - Why informal probability arguments fail
   - The importance of precise definitions
   - The difficulty of proving lower bounds

## Structure

```
figueroa-2016-pneqnp/
├── README.md           (this file)
├── coq/               (Coq formalization)
│   └── Figueroa2016.v
├── lean/              (Lean 4 formalization)
│   └── Figueroa2016.lean
└── isabelle/          (Isabelle/HOL formalization)
    └── Figueroa2016.thy
```

## Educational Value

This formalization demonstrates:

1. **The power of type systems**: The type error in function signatures is immediately caught
2. **Precision requirements**: Formal proofs require completely unambiguous definitions
3. **Proof obligation tracking**: Every claim must be justified; gaps are immediately visible
4. **The difficulty of complexity lower bounds**: Proving "no algorithm exists" is fundamentally different from showing an algorithm doesn't exist in some restricted class

## References

1. Arroyo-Figueroa, J.A. (2016). "The Existence of the Tau One-Way Functions Class as a Proof that P != NP". arXiv:1604.03758v4.

2. Juvekar, M., Narváez, D.E., & Welsh, M. (2021). "On Arroyo-Figueroa's Proof that P ≠ NP". arXiv:2103.15246.

3. Goldreich, O. (2001). "Foundations of Cryptography: Volume 1, Basic Tools". Cambridge University Press. (Standard reference for one-way functions)

4. Naor, M., & Yung, M. (1989). "Universal one-way hash functions and their cryptographic applications". Proceedings of the Twenty-first Annual ACM Symposium on Theory of Computing.

## Related Issues

- Parent: #44 - Test all P vs NP attempts formally
- Source: #45 - Auto-generated issue template
