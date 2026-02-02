# Refutation: Jormakka 2008

This directory contains formalizations that demonstrate the critical errors in Jorma Jormakka's 2008 attempted proof of P ≠ NP.

## Contents

- `lean/JormakkaRefutation.lean` - Lean 4 formalization of the refutation
- `rocq/JormakkaRefutation.v` - Rocq (Coq) formalization of the refutation

## Summary of Errors

Jormakka's proof fails due to **multiple fundamental flaws**:

1. **Non-Uniform vs Uniform Lower Bounds** (Fatal)
2. **Circular Adversarial Construction** (Fatal)
3. **Algorithm-Dependent Instances** (Fatal)
4. **Relativization Barrier Violation** (Known impossible)

## Error 1: Non-Uniform vs Uniform Lower Bounds

### The Fatal Flaw

**What Jormakka proves**: ∀ algorithm A, ∃ instance I_A such that A is slow on I_A

**What's needed for P ≠ NP**: ∃ instance I such that ∀ algorithm A, A is slow on I

**These are logically different claims!**

### Why This Matters

- Jormakka's construction shows that **for each algorithm**, we can **find an instance** hard for that algorithm
- But different algorithms get different hard instances (I_A₁ ≠ I_A₂)
- This does NOT prove there exists a **single instance** hard for **all algorithms**

### Concrete Example

Consider two hypothetical algorithms:
- Algorithm A₁ is slow on instance I₁ but fast on I₂
- Algorithm A₂ is slow on instance I₂ but fast on I₁

Jormakka's claim: "A₁ has a hard instance (I₁) and A₂ has a hard instance (I₂)"

But this doesn't prove any instance is hard for both! In fact, this example shows there may be **no universally hard instance**.

### The Formalization

The formalizations prove that `JormakkaProves → NeededForLowerBound → False`, showing these claims are incompatible. The implication from non-uniform to uniform is invalid.

## Error 2: Circular Adversarial Construction

### The Problem

Jormakka's Definition 3 constructs instances K₁, K₂, K₃ **after** choosing the algorithm, by:
1. Analyzing the algorithm's execution behavior
2. Selecting j'ᵢ values that take "at least as long as the median computation time" for **this specific algorithm**
3. Constructing instances based on this analysis

### Why This Is Circular

**The Construction Process:**
1. Goal: Prove algorithm A is slow
2. Method: Construct instance I by selecting inputs that are slow for A
3. Observation: A is slow on I
4. Conclusion: Therefore A is slow

**This proves nothing!** Of course A is slow on I - we specifically designed I to be slow for A!

### Analogy

It's like trying to prove "all students struggle with math" by:
1. For each student, analyze what they're bad at
2. Give them a test specifically on their weaknesses
3. Observe they struggle
4. Conclude all students struggle with math

This proves nothing about the intrinsic difficulty of math - only that we can tailor tests to student weaknesses.

### The Formalization

The formalization shows that assuming `adversarial_construction_assumes_slowness` leads to circular reasoning. The construction **assumes** the algorithm is slow by selecting slow inputs, which is precisely what we're trying to prove.

## Error 3: Algorithm-Dependent Construction

### The Problem

Jormakka's Definitions 3-5 construct different instances for different algorithms:
- The construction analyzes the algorithm's branching structure (Lemma 5, Remark 2)
- Different algorithms have different branching patterns
- Therefore different algorithms get different K₁, K₂, K₃ instances

### Why This Invalidates the Proof

Because the "hard instances" are tailored to each algorithm, we cannot conclude there exists a universally hard instance. A polynomial-time algorithm might exist that avoids all the algorithm-specific instances constructed for other algorithms.

### The Formalization

The formalization proves `adversarial_construction_depends_on_algorithm`, showing that for different algorithms tm1 and tm2, the constructed instances are different. This algorithm-dependence breaks the logical chain to P ≠ NP.

## Error 4: Relativization Barrier

### The Known Barrier

Baker-Gill-Solovay (1975) proved that:
- There exist oracles A where P^A = NP^A
- There exist oracles B where P^B ≠ NP^B
- Therefore any proof technique that "relativizes" (works the same in all oracle worlds) cannot resolve P vs NP

### Why Jormakka's Proof Relativizes

Jormakka's construction works the same way regardless of what oracle we add:
- The adversarial construction can be applied in any oracle world
- The recurrence argument doesn't depend on the oracle
- Therefore the proof "relativizes"

### The Consequence

Since the proof relativizes, and there exist oracles where P = NP, Jormakka's proof technique **cannot possibly** separate P from NP. It's hitting a known impossible barrier.

### The Formalization

The formalization shows that `construction_relativizes` together with `baker_gill_solovay` implies the proof cannot work.

## What Would Be Required for a Valid Proof

To validly prove P ≠ NP via this approach, one would need:

### 1. Uniform Lower Bound

**Define instances independent of the algorithm**, then prove **all algorithms** are slow on these instances.

```
∃ instance I such that ∀ algorithm A, A is slow on I
```

Not Jormakka's claim:

```
∀ algorithm A, ∃ instance I_A such that A is slow on I_A
```

### 2. Non-Circular Construction

Construct hard instances **without** analyzing how specific algorithms perform on them. The instances must be defined **before** considering any algorithm.

### 3. Universal Argument

Show that **any algorithm** solving subset sum must perform certain operations, establishing an unavoidable lower bound that applies to **all possible algorithms simultaneously**.

### 4. Barrier Circumvention

The technique must overcome:
- Relativization barrier (Baker-Gill-Solovay, 1975)
- Natural proofs barrier (Razborov-Rudich, 1997)
- Algebrization barrier (Aaronson-Wigderson, 2008)

## Educational Value

This attempt illustrates several important lessons:

### 1. Quantifier Order Matters

`∀A ∃I` is fundamentally different from `∃I ∀A`. The order of quantifiers changes the meaning completely.

### 2. Circular Arguments

You cannot prove hardness by constructing adversarial instances tailored to each algorithm. The instances must be defined independently.

### 3. Non-Uniform vs Uniform

Non-uniform arguments (different instances for different algorithms) do not imply uniform results (single instance for all algorithms).

### 4. Known Barriers

Certain proof strategies are known to be impossible. Attempting them wastes effort. Jormakka's approach appears to violate the relativization barrier.

## The Analogy: Puzzles and Solvers

The formalizations include this analogy:

**Jormakka's approach**: "For each puzzle solver, I can find a puzzle they struggle with"
- Of course! I just ask them what they're bad at and give them that puzzle.
- This proves nothing about puzzles being inherently hard.

**Correct approach**: "There exists a puzzle that all solvers struggle with"
- This would actually prove the puzzle is inherently hard.
- This is what's needed, but not what Jormakka proves.

## Conclusion

Jormakka's proof fails because it uses a **non-uniform, adversarial, algorithm-dependent construction**. The "hard instances" are tailored to each algorithm after analyzing its behavior. This is fundamentally different from proving that subset sum is intrinsically hard for all algorithms.

The proof demonstrates:
```
∀ algorithm A, ∃ hard instance I_A for A
```

But to prove P ≠ NP, we need:
```
∃ hard instance I for all algorithms A
```

These are logically distinct, and the former does not imply the latter.

## See Also

- [`../README.md`](../README.md) - Complete overview and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../proof/README.md`](../proof/README.md) - Forward formalization showing what Jormakka actually proves
