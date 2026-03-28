# Error Analysis: Vega (2015) P = NP via equivalent-P

## Quick Summary

**Fatal Flaw**: Confusing subset relationship (⊆) with equality (=) of complexity classes.

**What Vega Actually Proved**: P ⊆ ∼P and NP ⊆ ∼P (via diagonal embeddings)

**What Vega Claimed**: ∼P = P and ∼P = NP, therefore P = NP

**Why This is Wrong**: Two sets can both be subsets of a third set without being equal to each other.

## Detailed Error Breakdown

### 1. The Diagonal Construction Mistake

Vega defines:
- ∼ONE-IN-THREE 3SAT = {(φ,φ) : φ ∈ ONE-IN-THREE 3SAT}
- ∼HORNSAT = {(φ,φ) : φ ∈ HORNSAT}

**Problem**: These are trivial self-pairings, not meaningful examples of "two different problems sharing a solution."

**Analogy**: It's like saying "I found that problem A can work with itself" instead of "I found two different problems A and B that interact."

### 2. The Subset vs. Equality Error

**Vega's Logic (INCORRECT)**:
1. I can embed NP-complete problems in ∼P → Therefore ∼P = NP
2. I can embed P-complete problems in ∼P → Therefore ∼P = P
3. Therefore P = NP

**Correct Logic**:
1. Embedding NP-complete problems in ∼P → NP ⊆ ∼P (only a subset!)
2. Embedding P-complete problems in ∼P → P ⊆ ∼P (only a subset!)
3. Therefore: P ⊆ ∼P and NP ⊆ ∼P, which is consistent with BOTH P = NP AND P ≠ NP

**Counterexample**:
- Let P = {1} (just the problem "1")
- Let NP = {1, 2} (problems "1" and "2")
- Let ∼P = {1, 2, 3} (problems "1", "2", and "3")
- Then P ⊆ ∼P ✓
- And NP ⊆ ∼P ✓
- But P ≠ NP ✓

This shows that two different classes can both be subsets of a third class!

### 3. The Reduction Structure Breakdown

**Vega's Claim**: Since NP is closed under reductions, and I showed one NP-complete problem is in ∼P, all of NP is in ∼P.

**The Error**: The diagonal embedding DiagonalEmbedding(L) = {(x,x) : x ∈ L} does NOT preserve polynomial-time reductions!

**Why**:
- If L₁ reduces to L₂ via function f
- This means: x ∈ L₁ ⟺ f(x) ∈ L₂
- But DiagonalEmbedding(L₁) consists of pairs (x,x) where x ∈ L₁
- And DiagonalEmbedding(L₂) consists of pairs (y,y) where y ∈ L₂
- The reduction would need to map (x,x) to (f(x), f(x))
- But this only works if we apply f to BOTH components
- This is NOT the same as the original reduction from L₁ to L₂

**Conclusion**: Even though SAT reduces to every NP problem, DiagonalEmbedding(SAT) does NOT reduce to DiagonalEmbedding(L) for arbitrary L in NP.

### 4. The Verifier Confusion

**Vega's Definition of ∼P**: Languages of pairs (x,y) where x ∈ L₁ ∈ P, y ∈ L₂ ∈ P, and there exists a certificate z such that both x and y can be verified with z.

**Problem**: Problems in P don't naturally have "certificates" — they're decidable directly! The use of verifiers is characteristic of NP, not P.

**What This Means**:
- The definition of ∼P is awkward and doesn't capture a natural complexity class
- The diagonal examples {(φ,φ)} are degenerate cases that don't illuminate the structure
- It's unclear what ∼P actually represents without proper analysis

### 5. Mathematical Formalism of the Error

In formal logic, Vega's argument has this structure:

**Vega's Claims**:
1. ∃ L ∈ NP-complete such that DiagonalEmbedding(L) ∈ ∼P
2. ∃ L ∈ P-complete such that DiagonalEmbedding(L) ∈ ∼P
3. ∼P is closed under reductions
4. Therefore ∼P = NP and ∼P = P
5. Therefore P = NP

**The Errors**:
- **Step 1→4**: Even with closure under reductions, showing one element embeds doesn't prove the whole class equals ∼P. You would need to show:
  - Every problem in NP has its diagonal embedding in ∼P (possibly true)
  - Every problem in ∼P is the diagonal embedding of something in NP (NOT shown!)
- **Step 2→4**: Same error for P
- **Step 4→5**: Even if both were true, this would only show ∼P ⊇ P and ∼P ⊇ NP, not ∼P = P = NP

**What's Actually Proven**:
- ∀L ∈ P: DiagonalEmbedding(L) ∈ ∼P (i.e., P embeds in ∼P)
- ∀L ∈ NP: DiagonalEmbedding(L) ∈ ∼P (i.e., NP embeds in ∼P)
- These are consistent with P ≠ NP!

## Why This Error is Common

This type of error appears in many P vs NP attempts:

1. **Complexity class confusion**: Mixing up "a problem is in a class" with "a transformation of a problem is in a class"
2. **Subset vs. equality**: Not distinguishing between ⊆ and =
3. **Reduction closure misuse**: Assuming closure properties work for transformed problems
4. **Novel class pitfalls**: Defining a new complexity class without thoroughly analyzing its properties

## The Correct Approach

To actually prove P = NP using a new complexity class C, you would need:

1. **Show P ⊆ C**: Every problem in P is in C
2. **Show C ⊆ P**: Every problem in C is in P
3. **Show NP ⊆ C**: Every problem in NP is in C
4. **Show C ⊆ NP**: Every problem in C is in NP
5. From 1-4: C = P and C = NP, therefore P = NP

**What Vega Actually Did**:
- Showed: ∀L ∈ P, DiagonalEmbedding(L) ∈ ∼P (weaker than P ⊆ ∼P)
- Showed: ∀L ∈ NP, DiagonalEmbedding(L) ∈ ∼P (weaker than NP ⊆ ∼P)
- Did NOT show the reverse directions
- Did NOT account for the fact that DiagonalEmbedding changes the problem

## Formalization Results

Our formalizations in Rocq, Lean, and Isabelle all demonstrate:

1. ✅ We can define InEquivalentP formally
2. ✅ We can define DiagonalEmbedding formally
3. ✅ We can show that diagonal embeddings of P problems are in ∼P
4. ❌ We CANNOT prove that this implies ∼P = P
5. ❌ We CANNOT prove that P ⊆ ∼P and NP ⊆ ∼P implies P = NP

The formalization exposes the gap: the transition from "embeddings exist" to "classes are equal" is unjustified.

## Lessons for Complexity Theory

1. **Diagonal constructions** like x ↦ (x,x) are useful but don't create interesting new complexity structure
2. **Subset relationships** must be carefully distinguished from equality
3. **New complexity classes** require thorough analysis before being used in proofs
4. **Reduction closure** must be verified for transformed problems, not assumed
5. **Type checking in proof assistants** helps catch these logical errors early

## References

- Vega, F. (2015). "Solution of P versus NP Problem." HAL hal-01161668
- Our formalizations: rocq/VegaEquivalentP.v, lean/VegaEquivalentP.lean, isabelle/VegaEquivalentP.thy
