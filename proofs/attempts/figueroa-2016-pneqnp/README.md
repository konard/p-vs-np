# Figueroa (2016) - P≠NP Attempt

**Attempt ID**: 109
**Author**: Javier A. Arroyo-Figueroa
**Year**: 2016
**Claim**: P≠NP
**Status**: **REFUTED**

## References

- **Original Paper**: [arXiv:1604.03758](https://arxiv.org/abs/1604.03758) - "The Existence of the Tau One-Way Functions Class as a Proof that P != NP"
- **Critique Paper**: [arXiv:2103.15246](https://arxiv.org/abs/2103.15246) - "On Arroyo-Figueroa's Proof that P ≠ NP" by Mandar Juvekar, David E. Narváez, and Melissa Welsh (March 2021)
- **Woeginger's List**: Entry #109 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

In April 2016, Javier A. Arroyo-Figueroa claimed to prove that P ≠ NP by establishing the existence of a class of one-way functions called **Tau (τ)**. The main argument is:

1. Construct a class of functions τ, where each member is computable in polynomial time
2. Show that finding the inverse of any τ function has negligible probability for any polynomial probabilistic algorithm
3. Prove that no polynomial-time algorithm exists to compute the inverse of τ functions
4. Conclude that the existence of such one-way functions implies P ≠ NP

The approach relies on constructing each member in τ using:
- A collection of independent universal hash functions
- Random bit matrices that produce starting coordinates and paths
- A sequence of unique random bit matrices

## Main Argument Structure

### The Claimed Construction

1. **Function Definition**: Define a class τ of functions where each τ ∈ Τ maps bit sequences
2. **Polynomial-Time Computation**: Show that each τ can be computed in polynomial time
3. **Inverse Hardness**: Argue that finding τ⁻¹(y) for a given y is computationally infeasible
4. **One-Way Property**: Conclude that τ functions satisfy the definition of one-way functions
5. **P≠NP Conclusion**: Use the existence of one-way functions to prove P ≠ NP

### The Relationship to P vs NP

The proof relies on the well-known fact that:
- **If one-way functions exist, then P ≠ NP**

This is because if P = NP, then every function computable in polynomial time would also have its inverse computable in polynomial time (for decision problems), which contradicts the one-way property.

## The Error in the Proof

According to the critique by Juvekar, Narváez, and Welsh (2021), the proof contains a **critical function mapping error**:

### Main Flaw: Function Domain/Codomain Mismatch

1. **Claimed Mapping**: The paper claims each τ function maps {0,1}ⁿ → {0,1}ⁿ
   - Input: bit sequence of length n
   - Output: bit sequence of length n

2. **Actual Mapping**: The algorithm actually produces {0,1}ⁿ → {0,1}ⁿ²
   - The construction appends n bits for every bit in the input sequence
   - This means the output has n² bits, not n bits

### Consequences of This Error

This inconsistency has several critical implications:

1. **Incorrect Preimage Size Calculations**: The proof incorrectly calculates the size of hash function preimages
   - Expected preimage size: 2ⁿ (for n-bit outputs)
   - Actual preimage size: 2ⁿ² (for n²-bit outputs)
   - This affects probability calculations by an exponential factor

2. **Flawed Probability Analysis**: The probability of randomly selecting an input that maps to a given output is wrong
   - Claimed probability: ~1/2ⁿ
   - Actual probability: ~1/2ⁿ²
   - This invalidates the "negligible probability" argument

3. **Broken One-Way Function Proof**: Without correct probability bounds, the proof fails to establish that τ functions are truly one-way

4. **Invalid P≠NP Conclusion**: Since the existence of one-way functions is not proven, the P≠NP conclusion does not follow

## Formalization Strategy

To formalize this proof attempt and expose the error, we:

1. **Define the basic concepts**:
   - Polynomial-time computability
   - One-way functions
   - The relationship between OWFs and P vs NP

2. **Formalize the τ function construction**:
   - Model the hash function composition
   - Model the bit matrix operations
   - Carefully track input/output sizes

3. **Attempt to prove the one-way property**:
   - Formalize the probability calculations
   - Expose the domain/codomain mismatch
   - Show where the proof breaks down

4. **Document the gap**:
   - Make the error explicit in the formal proof
   - Show that the claimed property cannot be proven with the given construction

## Key Insights

1. **Careful type checking matters**: The error would have been caught immediately in a strongly-typed formal system
2. **Asymptotic analysis is subtle**: Confusing n with n² in complexity analysis leads to exponential errors
3. **Probability calculations require precision**: Small mistakes in probability bounds can invalidate cryptographic arguments
4. **One-way functions remain unproven**: This failed attempt highlights why OWFs are still a major open problem

## Lessons for Formal Verification

This case study demonstrates:
- The value of formal type systems in catching domain/codomain errors
- The importance of tracking exact sizes in complexity arguments
- How formalization can expose subtle errors in probability calculations
- Why proposed P vs NP proofs require extremely careful verification

## Status of Formalization

- **Coq**: Partial formalization with error exposed
- **Lean**: Partial formalization with error exposed
- **Isabelle**: Partial formalization with error exposed

All three formalizations deliberately expose the function mapping error that invalidates the proof.
