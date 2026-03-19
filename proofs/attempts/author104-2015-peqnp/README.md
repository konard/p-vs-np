# Formalization: Frank Vega (2015) - P = NP via equivalent-P

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

**Attempt ID**: 104
**Author**: Frank Vega
**Year**: 2015
**Claim**: P = NP
**Paper**: "Solution of P versus NP Problem"
**Source**: [HAL Archive hal-01161668](https://hal.science/hal-01161668)
**Woeginger's List**: Entry #104 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

In June 2015, Frank Vega introduced a new complexity class called **equivalent-P** (denoted ∼P), which has a close relation to the P versus NP question. The class ∼P contains languages of ordered pairs of instances where each instance belongs to a specific problem in P, such that the two instances share the same solution (certificate).

Vega's argument proceeds in three steps:
1. Define the complexity class ∼P
2. Show that ∼P = NP (Theorem 5.3)
3. Show that ∼P = P (Theorem 6.2)
4. Conclude that P = NP (Theorem 6.3)

## Main Definitions

### Equivalent-P (∼P) Class

**Definition 3.1**: Given two languages L₁ and L₂ in P with verifiers M₁ and M₂, a language L belongs to ∼P if:

```
L = {(x, y) : ∃z such that M₁(x,z) = "yes" and M₂(y,z) = "yes" where x ∈ L₁ and y ∈ L₂}
```

In other words, ∼P contains ordered pairs of problem instances from P that share the same certificate.

### E-reduction

**Definition 4.1**: A language L₁ is e-reducible to a language L₂, written L₁ ≤∼ L₂, if there exist two logarithmic-space computable functions f and g such that for all x and y:

```
(x, y) ∈ L₁ if and only if (f(x), g(y)) ∈ L₂
```

## Main Argument

### Step 1: ∼P = NP (Theorem 5.3)

Vega defines:
- **∼ONE-IN-THREE 3SAT** = {(φ, φ) : φ ∈ ONE-IN-THREE 3SAT}
- **3XOR-2SAT** = {(ψ, φ) : ψ ∈ XOR 3SAT and φ ∈ 2SAT with same satisfying assignment}

He shows ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT (Theorem 5.2) and claims this implies ∼P = NP.

### Step 2: ∼P = P (Theorem 6.2)

Vega defines:
- **∼HORNSAT** = {(φ, φ) : φ ∈ HORNSAT}

He shows ∼HORNSAT ∈ ∼P (Theorem 6.1) and claims this implies ∼P = P.

### Step 3: P = NP (Theorem 6.3)

From ∼P = NP and ∼P = P, Vega concludes P = NP.

## The Critical Errors

The proof contains multiple fundamental flaws that invalidate the argument:

### 1. Definition Inconsistency and Ill-Formed Definition

The definition of ∼P (Definition 3.1) is problematic:

**Confusion Between Verifiers and Deciders**: The definition states that M₁ and M₂ are "verifiers" of L₁ and L₂ where L₁, L₂ ∈ P. However:
- Problems in P are decidable in polynomial time by deterministic Turing machines
- They don't require certificates or verifiers in the NP sense
- For any L ∈ P, we can define a "verifier" M that ignores the certificate z and simply decides x ∈ L

This makes the certificate z either **meaningless** (if ignored) or introduces a **non-standard constraint** unrelated to computational complexity.

### 2. The Diagonal Construction Fallacy

Vega uses diagonal constructions {(φ,φ) : φ ∈ L} for both:
- ∼ONE-IN-THREE 3SAT (to show ∼P = NP)
- ∼HORNSAT (to show ∼P = P)

**Problem**: These are NOT examples of "two instances from different problems sharing a certificate"—they are trivial examples where "one instance shares a certificate with itself." This doesn't create a meaningful new complexity class, as any language L can be embedded as {(x,x) : x ∈ L}.

### 3. Type Mismatch

The complexity classes are incomparable:
- **∼P** consists of languages over ordered pairs (x, y)
- **P and NP** consist of languages over single strings

The claim ∼P = NP confuses:
- The class of languages {(x, x) : x ∈ L} for L ∈ NP
- The class NP itself

### 4. Insufficient Closure Arguments

Theorems 5.3 and 6.2 each show one problem is in ∼P but don't establish that ∼P equals P or NP. The logic "if a complete problem is in C, then C equals the class" requires:
- C is closed under reductions (✓ shown in Theorem 4.2)
- The reduction type matches (✗ e-reductions ≠ polynomial-time reductions ≠ log-space reductions)
- The language types match (✗ pairs ≠ single instances)

### 5. The Transitivity Trap

The proof attempts to show:
- NP ⊆ ∼P (via ∼ONE-IN-THREE 3SAT)
- P ⊆ ∼P (via ∼HORNSAT)

Even if both were true, this would only show that both P and NP are subsets of ∼P—NOT that P = NP. It would only show that ∼P is a common upper bound.

### 6. No Meaningful Complexity Barrier Overcome

The construction essentially creates syntactic pairs without addressing why problems in NP are believed to be harder than problems in P. The known barriers (relativization, natural proofs, algebrization) are not addressed.

## Formalization Goals

The formalizations in Rocq, Lean, and Isabelle aim to:

1. Define the complexity class ∼P as stated in Definition 3.1
2. Attempt to formalize the key theorems (4.2, 5.2, 5.3, 6.1, 6.2, 6.3)
3. Identify where the formalization breaks down or reveals the error
4. Make the type mismatches and logical gaps explicit
5. Show the gap: Proving L has an embedding into ∼P does NOT imply L = ∼P

The formalization should reveal that the definition of ∼P is either:
- Vacuous (if certificates can be ignored), or
- Incomparable to P and NP (if certificates matter)

In either case, the claimed equalities ∼P = P and ∼P = NP cannot be established in the way presented in the paper.

## Files

- [`ERROR_ANALYSIS.md`](ERROR_ANALYSIS.md) - Detailed error analysis
- [`rocq/VegaAttempt.v`](rocq/VegaAttempt.v) - Rocq formalization (original)
- [`rocq/VegaEquivalentP.v`](rocq/VegaEquivalentP.v) - Alternative Rocq formalization
- [`lean/VegaAttempt.lean`](lean/VegaAttempt.lean) - Lean 4 formalization (original)
- [`lean/VegaEquivalentP.lean`](lean/VegaEquivalentP.lean) - Alternative Lean formalization
- [`isabelle/VegaAttempt.thy`](isabelle/VegaAttempt.thy) - Isabelle/HOL formalization (original)
- [`isabelle/VegaEquivalentP.thy`](isabelle/VegaEquivalentP.thy) - Alternative Isabelle formalization

## Known Refutation

This proof attempt does not appear to have been formally published in a peer-reviewed venue. It was uploaded to HAL (an open preprint archive) in June 2015.

The error is a definitional one: the complexity class ∼P is not well-defined in a way that makes it meaningfully comparable to P and NP. The attempt to bridge these classes through specific problem instances (∼HORNSAT, ∼ONE-IN-THREE 3SAT) fails because:

1. The reduction types don't match the standard reductions for P and NP
2. The language types (pairs vs. single instances) don't match
3. The notion of "shared certificate" for problems in P is vacuous

## Complexity Theory Lessons

This attempt illustrates several common pitfalls in P vs NP attempts:

1. **Defining new complexity classes**: Without careful analysis, new classes can be ill-defined or trivial
2. **Diagonal constructions**: The map L → {(x,x) : x ∈ L} preserves complexity but doesn't create meaningful new structure
3. **Subset vs. equality**: Showing L₁, L₂ ⊆ L₃ does NOT imply L₁ = L₂
4. **Closure under reductions**: Must be applied carefully with the correct reduction type
5. **Verifiers vs. deciders**: P is characterized by efficient decision, NP by efficient verification

## References

- Frank Vega, "Solution of P versus NP Problem", HAL preprint hal-01161668, June 2015
- https://hal.science/hal-01161668
- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Status

- ✅ Paper analyzed
- 🚧 Rocq formalization: Has compilation errors (type unification issue)
- ✅ Lean formalization: Complete
- ✅ Isabelle formalization: Complete
- ✅ Error identified and documented

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Documentation](../../../P_VS_NP_TASK_DESCRIPTION.md)
