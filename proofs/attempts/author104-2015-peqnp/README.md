# Formalization: Vega (2015) - P = NP via equivalent-P

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

**Attempt ID**: 104
**Author**: Frank Vega
**Year**: 2015
**Claim**: P = NP
**Paper**: "Solution of P versus NP Problem"
**Source**: [HAL Archive hal-01161668](https://hal.science/hal-01161668)
**Woeginger's List**: Entry #104

## Summary

In June 2015, Frank Vega introduced a new complexity class called **equivalent-P** (denoted ∼P), which has a close relation to the P versus NP question. The class ∼P contains languages of ordered pairs of instances where each instance belongs to a specific problem in P, such that the two instances share the same solution (certificate).

Vega attempts to demonstrate that:
1. ∼P = NP (Theorem 5.3)
2. ∼P = P (Theorem 6.2)

From these two claims, he concludes P = NP (Theorem 6.3).

## The Main Argument

### Definition of ∼P (equivalent-P)

Given two languages L₁ and L₂ in P with verifiers M₁ and M₂, a language L belongs to ∼P if:

```
L = {(x, y) : ∃z such that M₁(x,z) = "yes" and M₂(y,z) = "yes" where x ∈ L₁ and y ∈ L₂}
```

In other words, ∼P contains ordered pairs of problem instances from P that share the same certificate.

### Key Reductions

1. **∼ONE-IN-THREE 3SAT**: Defined as {(φ,φ) : φ ∈ ONE-IN-THREE 3SAT}, claimed to be NP-complete
2. **3XOR-2SAT**: Pairs (ψ,ϕ) where ψ ∈ XOR 3SAT and ϕ ∈ 2SAT with same satisfying assignment
3. **∼HORNSAT**: Defined as {(φ,φ) : φ ∈ HORNSAT}, claimed to be P-complete

### Proof Structure

1. Show ∼P is closed under e-reductions (Theorem 4.2)
2. Reduce ∼ONE-IN-THREE 3SAT to 3XOR-2SAT (Theorem 5.2)
3. Show 3XOR-2SAT ∈ ∼P, conclude ∼P = NP (Theorem 5.3)
4. Show ∼HORNSAT ∈ ∼P, conclude ∼P = P (Theorem 6.2)
5. Conclude P = NP (Theorem 6.3)

## The Critical Error

### Main Flaw: Circular Definition and Category Error

The proof contains a fundamental logical error in the definition and application of ∼P:

#### 1. Definition Inconsistency

The definition of ∼P (Definition 3.1) states that a language L belongs to ∼P when:
- L consists of ordered pairs (x, y)
- There exist TWO languages L₁ and L₂ in P
- There exists a shared certificate z

However, Vega's key examples violate this definition:

**∼HORNSAT = {(φ,φ) : φ ∈ HORNSAT}**

This is NOT a language of pairs from two different problems in P sharing a certificate. Rather, it's a language of identical pairs from a single problem. The definition requires L₁ and L₂ to be given first, then L is defined based on them. But ∼HORNSAT doesn't fit this pattern—it's defined by taking diagonal pairs from a single language.

#### 2. The Diagonal Construction Fallacy

Vega uses diagonal constructions {(φ,φ) : φ ∈ L} for both:
- ∼ONE-IN-THREE 3SAT (to show ∼P = NP)
- ∼HORNSAT (to show ∼P = P)

This creates a category error:
- These are not examples of "two instances from different problems sharing a certificate"
- They are trivial examples where "one instance shares a certificate with itself"
- Any language L can be embedded as {(x,x) : x ∈ L}, which doesn't create a meaningful new complexity class

#### 3. The Transitivity Trap

The proof attempts to show:
- NP ⊆ ∼P (via ∼ONE-IN-THREE 3SAT)
- P ⊆ ∼P (via ∼HORNSAT)

Even if both were true, this would only show that both P and NP are subsets of ∼P. This does NOT imply P = NP. It would only show that ∼P is a common upper bound, which could simply mean ∼P is large (potentially equal to NP or even larger).

#### 4. The Verifier Confusion

Definition 3.1 requires that L₁ and L₂ be in P and have verifiers M₁ and M₂. However:
- Problems in P are decision problems that can be *decided* in polynomial time
- The use of "verifiers" suggests NP (where verification is the key concept)
- The definition conflates "being in P" with "having a polynomial-time verifier"

While every problem in P trivially has a polynomial-time verifier (ignore the certificate, just solve the problem), this is not the standard way to characterize P, and it obscures what ∼P actually represents.

#### 5. Incorrect Claim: ∼P = NP

Theorem 5.3 claims ∼P = NP based on:
- Showing ∼ONE-IN-THREE 3SAT ∈ ∼P
- Using closure under reductions

**Problem**: The proof only shows NP has *some* problems that can be embedded in ∼P via the diagonal construction. It does NOT show:
- That every problem in NP is in ∼P
- That every problem in ∼P is in NP

The correct conclusion would be that ∼ONE-IN-THREE 3SAT ∈ ∼P, not that all of NP equals ∼P.

#### 6. Incorrect Claim: ∼P = P

Theorem 6.2 claims ∼P = P based on:
- Showing ∼HORNSAT ∈ ∼P
- Using closure under reductions

**Problem**: The same error as above—showing one P-complete problem can be embedded in ∼P does not prove ∼P = P.

### What ∼P Actually Represents

If we interpret the definition strictly, ∼P appears to be related to:
- Languages of pairs that share solutions
- This is similar to the complexity class of finding common satisfying assignments
- It's unclear what the complexity of ∼P actually is without a proper analysis

The diagonal examples {(x,x) : x ∈ L} are degenerate cases that don't illuminate the structure of ∼P.

## Formalization Goals

Our formalization will:

1. **Define ∼P precisely** in each proof assistant
2. **Formalize the diagonal construction** {(x,x) : x ∈ L}
3. **Show the gap**: Proving L has an embedding into ∼P does NOT imply L = ∼P
4. **Demonstrate the error**: Show that the argument structure "L₁ ⊆ ∼P and L₂ ⊆ ∼P implies L₁ = L₂" is invalid
5. **Characterize ∼P properly**: Determine what ∼P actually is (likely ∼P = NP, but via different reasoning)

## Files

- `coq/VegaEquivalentP.v` - Coq formalization showing the flaw
- `lean/VegaEquivalentP.lean` - Lean 4 formalization showing the flaw
- `isabelle/VegaEquivalentP.thy` - Isabelle/HOL formalization showing the flaw

## Known Refutation

This proof has not been accepted by the complexity theory community. The main issues are:

1. **Definitional problems**: The definition of ∼P and its diagonal embeddings are not properly justified
2. **Logical gap**: The transition from "some problems in P and NP can be embedded in ∼P" to "P = ∼P = NP" is unjustified
3. **Lack of peer review**: Published only as a preprint, not peer-reviewed
4. **No response to barriers**: Does not address known barriers (relativization, natural proofs, algebrization)

## Complexity Theory Lessons

This attempt illustrates several common pitfalls in P vs NP attempts:

1. **Defining new complexity classes**: Without careful analysis, new classes can be ill-defined or trivial
2. **Diagonal constructions**: The map L → {(x,x) : x ∈ L} preserves complexity but doesn't create meaningful new structure
3. **Subset vs. equality**: Showing L₁, L₂ ⊆ L₃ does NOT imply L₁ = L₂
4. **Closure under reductions**: Must be applied carefully with the correct reduction type
5. **Verifiers vs. deciders**: P is characterized by efficient decision, NP by efficient verification

## References

- Vega, F. (2015). "Solution of P versus NP Problem." HAL preprint hal-01161668. https://hal.science/hal-01161668
- Woeginger, G. J. "The P-versus-NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Status

- ✅ Paper analyzed
- 🚧 Coq formalization: In progress
- 🚧 Lean formalization: In progress
- 🚧 Isabelle formalization: In progress
- ✅ Error identified and documented

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Documentation](../../../P_VS_NP_TASK_DESCRIPTION.md)
