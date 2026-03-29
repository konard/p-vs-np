# Forward Proof Formalization: Jormakka 2008

This directory contains the forward formalization of Jorma Jormakka's 2008 attempted proof of P ≠ NP, following the paper's argument as faithfully as possible.

## Contents

- `lean/JormakkaProof.lean` - Lean 4 formalization of the proof structure
- `rocq/JormakkaProof.v` - Rocq (Coq) formalization of the proof structure

## What These Formalizations Capture

The formalizations attempt to capture Jormakka's proof strategy:

1. **The Subset Sum Problem**: The decision version of subset sum, which is NP-complete
2. **The Complexity Measure f(n)**: Definition 2's "worst in the median" measure computed over instances without solutions
3. **Adversarial Instance Construction**: Definitions 3-5 constructing instances K₁, K₂, K₃ based on algorithm behavior
4. **The Recurrence Relation**: Lemma 15's claim that f(n) ≥ (n/2)f(n/2)
5. **Super-Polynomial Growth**: Lemmas 1-2 showing the recurrence implies super-polynomial growth
6. **The Conclusion**: The attempted proof that no polynomial-time algorithm exists for subset sum

## The Attempted Proof Logic

Jormakka's argument proceeds:

1. **Define f(n)** (Definition 2): Maximum median computation time over all n-tuples without solutions
2. **Construct adversarial instances** (Definition 3): Given algorithm A, build K₁,ⱼₙ with n/2 subproblems
3. **Claim non-reusability** (Lemma 5): Argue the n/2 subproblems must be solved separately by A
4. **Transform instances** (Definitions 4-5): Build K₃ and K₂ from K₁ to handle varying bit patterns
5. **Establish recurrence** (Lemma 15): Show f(n) ≥ (n/2)f(n/2) for the constructed instances
6. **Derive super-polynomial growth** (Lemmas 1-2): Prove the recurrence implies f(n) grows super-polynomially
7. **Conclude P ≠ NP**: Therefore subset sum requires super-polynomial time, implying P ≠ NP

## Key Aspects of the Construction

### Algorithm-Dependent Instances

The critical feature formalized here is that the construction of "hard instances" K₁, K₂, K₃ **depends on the specific algorithm being analyzed**:

- The construction analyzes the algorithm's branching structure (Lemma 5, Remark 2)
- It selects j'ᵢ values that take "at least as long as the median computation time" for **this specific algorithm**
- Different algorithms yield different instance constructions

### The Recurrence Relation

The formalization captures the recurrence f(n) ≥ (n/2)f(n/2), which is central to the proof. This recurrence, if valid, would indeed imply super-polynomial growth.

### The Median Complexity Measure

Definition 2's f(n) measure is formalized as:
- Maximum over all n-tuples
- Of the median computation time
- Over instances without solutions

This is a non-standard complexity measure specific to Jormakka's approach.

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at critical points where:

1. **The construction is algorithm-dependent**: Different algorithms get different instances
2. **The recurrence claim**: The step from adversarial construction to the recurrence relation
3. **The final conclusion**: The leap from the recurrence to P ≠ NP

These placeholders mark locations where the argument cannot be completed because the logical gap becomes insurmountable.

## Mathematical Validity vs Logical Validity

It's important to note:

- **The recurrence math is valid**: If f(n) ≥ (n/2)f(n/2), then f grows super-polynomially (Lemmas 1-2 are correct)
- **The construction is well-defined**: Given an algorithm, we can construct adversarial instances for it
- **The logical inference is invalid**: The construction being algorithm-dependent means the conclusion doesn't follow

The formalizations separate these concerns, showing where the mathematics works but the logic fails.

## Relation to the Refutation

See [`../refutation/README.md`](../refutation/README.md) for a detailed explanation of why this proof strategy cannot work. The key issue is that the construction is **non-uniform** (different algorithms get different instances) rather than **uniform** (a single instance hard for all algorithms).

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Detailed explanation of why the proof fails
