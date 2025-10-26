# Frank Vega's 2015 P=NP Proof Attempt

**Attempt ID**: 104
**Author**: Frank Vega
**Year**: 2015
**Claim**: P = NP
**Paper**: "Solution of P versus NP Problem"
**Source**: https://hal.science/hal-01161668
**Woeginger's List**: Entry #104 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

In June 2015, Frank Vega introduced a new complexity class called **equivalent-P** (denoted ∼P), which contains languages of ordered pairs of instances where each instance belongs to a specific problem in P, such that the two instances share the same solution (certificate).

Vega's argument proceeds in three steps:
1. Define the complexity class ∼P
2. Show that ∼P = NP (Theorem 5.3)
3. Show that ∼P = P (Theorem 6.2)
4. Conclude that P = NP (Theorem 6.3)

## Main Definitions

### Equivalent-P (∼P) Class

**Definition 3.1**: Given two languages L₁ and L₂, and two Turing machines M₁ and M₂, such that L₁ ∈ P and L₂ ∈ P where M₁ and M₂ are the verifiers of L₁ and L₂ respectively, a language L belongs to ∼P if:

```
L = {(x, y) : ∃z such that M₁(x,z) = "yes" and M₂(y,z) = "yes" where x ∈ L₁ and y ∈ L₂}
```

### E-reduction

**Definition 4.1**: A language L₁ is e-reducible to a language L₂, written L₁ ≤∼ L₂, if there exist two logarithmic-space computable functions f and g such that for all x and y:

```
(x, y) ∈ L₁ if and only if (f(x), g(y)) ∈ L₂
```

## Main Argument

### Step 1: ∼P = NP (Theorem 5.3)

Vega defines:
- ∼ONE-IN-THREE 3SAT = {(φ, φ) : φ ∈ ONE-IN-THREE 3SAT}
- 3XOR-2SAT = {(ψ, φ) : ψ ∈ XOR 3SAT and φ ∈ 2SAT with same satisfying assignment}

He shows ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT (Theorem 5.2) and claims this implies ∼P = NP.

### Step 2: ∼P = P (Theorem 6.2)

Vega defines:
- ∼HORNSAT = {(φ, φ) : φ ∈ HORNSAT}

He shows ∼HORNSAT ∈ ∼P (Theorem 6.1) and claims this implies ∼P = P.

### Step 3: P = NP (Theorem 6.3)

From ∼P = NP and ∼P = P, Vega concludes P = NP.

## The Error

The fundamental error in Vega's proof is a **definition error** that leads to a **trivial collapse** of the complexity class ∼P.

### Critical Flaw: Confusion Between Verifiers and Deciders

The definition of ∼P (Definition 3.1) is problematic. It states that M₁ and M₂ are "verifiers" of L₁ and L₂ where L₁, L₂ ∈ P. However:

1. **Problems in P don't need certificates**: Languages in P are decidable in polynomial time by deterministic Turing machines. They don't require certificates or verifiers in the NP sense.

2. **The "verifier" concept is trivial for P**: For any L ∈ P, we can define a "verifier" M that ignores the certificate z and simply decides x ∈ L in polynomial time. Thus, the certificate z is meaningless.

### Why This Makes ∼P Trivial

Given the definition of ∼P, let's analyze what languages actually belong to this class:

For any pair (x, y) where x ∈ L₁ and y ∈ L₂ (both in P), the condition is:
```
∃z such that M₁(x,z) = "yes" and M₂(y,z) = "yes"
```

Since L₁, L₂ ∈ P, the machines M₁ and M₂ can decide membership without using z. The existence of a shared certificate z is either:
- **Always true** (if we allow the machines to ignore z and just decide membership), or
- **A non-trivial constraint** that has nothing to do with the computational complexity of L₁ and L₂

### The Vacuous Equality ∼P = P

In Theorem 6.1, Vega shows ∼HORNSAT ∈ ∼P by noting that for (φ, φ) ∈ ∼HORNSAT, both copies are equal, so they trivially share the same satisfying assignment (if one exists).

This is correct but reveals the problem: **∼P captures the wrong notion of "sharing solutions"**. It's not about computational complexity but about whether two problem instances happen to have the same certificate.

The claim ∼P = P (Theorem 6.2) is unjustified because:
- Showing one P-complete problem is in ∼P doesn't prove P ⊆ ∼P
- The definition of ∼P requires ordered pairs, while P contains single instances
- The reduction notion (e-reduction) is incomparable to the standard log-space reduction for P

### The Vacuous Equality ∼P = NP

Similarly, Theorem 5.3 claims ∼P = NP by showing ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT. However:

1. **∼ONE-IN-THREE 3SAT is artificially constructed**: The language {(φ, φ) : φ ∈ ONE-IN-THREE 3SAT} doesn't capture the computational complexity of NP-complete problems—it's just a syntactic pairing.

2. **The reduction preserves the wrong property**: The e-reduction preserves whether two instances share a certificate, not whether a single instance is in an NP-complete language.

3. **∼P ≠ NP on instances**: Languages in NP consist of single strings, while languages in ∼P consist of ordered pairs. The claim ∼P = NP confuses:
   - The class of languages {(x, x) : x ∈ L} for L ∈ NP
   - The class NP itself

### Summary of the Error

**The proof fails because**:

1. **Definition 3.1 is ill-formed**: It mixes the concept of polynomial-time decidability (for P) with polynomial-time verifiability (for NP) in a way that makes the certificate z either meaningless or non-standard.

2. **The complexity classes are incomparable**: ∼P consists of languages over ordered pairs with shared certificates, while P and NP consist of languages over single strings. The paper doesn't properly address this type mismatch.

3. **The closure arguments are insufficient**: Theorems 5.3 and 6.2 each show one problem is in ∼P but don't establish that ∼P equals P or NP. The logic "if a complete problem is in C, then C equals the class" requires:
   - C is closed under reductions (✓ shown in Theorem 4.2)
   - The reduction type matches (✗ e-reductions ≠ polynomial-time reductions ≠ log-space reductions)
   - The language types match (✗ pairs ≠ single instances)

4. **No meaningful complexity barrier is overcome**: The construction essentially creates syntactic pairs without addressing why problems in NP are believed to be harder than problems in P. The known barriers (relativization, natural proofs, algebrization) are not addressed.

## Formalization Goal

The formalizations in Coq, Lean, and Isabelle aim to:

1. Define the complexity class ∼P as stated in Definition 3.1
2. Attempt to formalize the key theorems (4.2, 5.2, 5.3, 6.1, 6.2, 6.3)
3. Identify where the formalization breaks down or reveals the error
4. Make the type mismatches and logical gaps explicit

The formalization should reveal that the definition of ∼P is either:
- Vacuous (if certificates can be ignored), or
- Incomparable to P and NP (if certificates matter)

In either case, the claimed equalities ∼P = P and ∼P = NP cannot be established in the way presented in the paper.

## Known Refutation

This proof attempt does not appear to have been formally published in a peer-reviewed venue. It was uploaded to HAL (an open preprint archive) in June 2015.

The error is a definitional one: the complexity class ∼P is not well-defined in a way that makes it meaningfully comparable to P and NP. The attempt to bridge these classes through specific problem instances (∼HORNSAT, ∼ONE-IN-THREE 3SAT) fails because:

1. The reduction types don't match the standard reductions for P and NP
2. The language types (pairs vs. single instances) don't match
3. The notion of "shared certificate" for problems in P is vacuous

## References

- Frank Vega, "Solution of P versus NP Problem", HAL preprint hal-01161668, June 2015
- https://hal.science/hal-01161668
- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## See Also

- [Coq formalization](coq/)
- [Lean formalization](lean/)
- [Isabelle formalization](isabelle/)
