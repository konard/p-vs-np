# Refutation: Plotnikov 2007

This directory contains formal refutations demonstrating why Plotnikov's 2007 P=NP attempt fails.

## Contents

- `lean/PlotnikovRefutation.lean` - Lean 4 refutation
- `rocq/PlotnikovRefutation.v` - Rocq refutation

## The Fatal Flaw

Plotnikov's algorithm for the Maximum Independent Set Problem (MISP) **depends on an unproven Conjecture 1**, making the P = NP claim invalid.

## Key Refutation Points

### 1. Conditional Correctness (The Main Error)

**From the paper (Theorem 5, page 9):**

> "**If the conjecture 1 is true** then the stated algorithm finds a MMIS of the graph G ∈ Lₙ."

**What this means:**
- The algorithm's correctness is CONDITIONAL on Conjecture 1
- Conjecture 1 is stated but NEVER PROVEN in the paper
- Without proving Conjecture 1, correctness is NOT established
- Therefore, the P = NP claim is INVALID

**Formalized as:**
```
algorithm_requires_conjecture :
  ∀ (AlgorithmCorrect Conjecture1 : Prop),
    (Conjecture1 → AlgorithmCorrect) ∧
    (¬ Conjecture1 → ¬ AlgorithmCorrect)
```

### 2. Empirical Testing Is Not Proof

**The author's defense (page 9):**

> "The pascal-programs were written for the proposed algorithm. Long testing the program for random graphs has shown that the algorithm runs stably and correctly."

**Why this fails:**
- Testing on random instances ≠ mathematical proof
- Counterexamples may exist outside the tested cases
- Mathematical claims require rigorous proof
- No amount of empirical validation replaces formal proof

**Formalized as:**
```
empirical_testing_insufficient :
  ¬ (∀ Conjecture, (∃ test_cases, ...) → Conjecture)
```

### 3. Circular Reasoning

The paper assumes the algorithm works correctly to derive properties that would make it work correctly. This is circular:

1. Algorithm works correctly → finds MMIS
2. Finds MMIS → Conjecture 1 must be true
3. Conjecture 1 true → Algorithm works correctly

This circular dependency invalidates the proof.

### 4. Unproven Conjecture 1

**The Conjecture (page 9):**

> "Let a saturated digraph G⃗(V⁰) has an independent set U ⊂ V such that Card(U) > Card(V⁰). Then it will be found a fictitious arc vᵢ ≫ vⱼ such that in the digraph G⃗(Z⁰), induced by removing this arc, the relation Card(Z⁰) ≥ Card(V⁰) - 1 is satisfied."

**Issues:**
- No proof provided
- No attempt to prove it
- No discussion of whether it's provable
- Essential to the algorithm's correctness

## Additional Refutation Points

### Issue 1: Dilworth's Theorem Application

**Problem**: Finding minimum chain partitions (MCP) is computationally hard

While Dilworth's Theorem guarantees existence of MCP, **computing it efficiently is non-trivial**:
- The Ford-Fulkerson correspondence requires careful justification
- Poset structure from graphs needs rigorous proof
- Efficiency claims are unverified

### Issue 2: Complexity Analysis Flaws

The O(n⁸) bound (Theorem 6) assumes:
- Exactly O(n) iterations needed (depends on Conjecture 1)
- Each iteration improves by 1 (unproven)
- No exponential blowup in special cases (assumed)

Without Conjecture 1, these assumptions collapse.

### Issue 3: MISP Remains NP-Complete

**Why polynomial-time MISP is hard:**
- Karp's 21 NP-complete problems (1972)
- Inapproximable within n^(1-ε) unless P=NP
- Decades of failed attempts
- Best known: exponential-time exact algorithms O(1.2^n)

## Why This Matters

If Plotnikov's algorithm were correct:
1. MISP would be solvable in polynomial time
2. Since MISP is NP-complete, P = NP would follow
3. This would win the $1 million Clay Millennium Prize
4. It would revolutionize computer science

**Reality:**
- The algorithm's correctness is not proven
- The proof depends on an unproven conjecture
- The claim remains unverified by the scientific community
- No rigorous proof exists

## The Formalizations

Both Lean and Rocq formalizations demonstrate:

1. **Conjecture Dependency**: Algorithm correctness requires Conjecture 1
2. **Unproven Status**: Conjecture 1 is never proven
3. **Empirical Insufficiency**: Testing ≠ proof
4. **Invalid Conclusion**: P = NP claim is not established

## Conclusion

Plotnikov's 2007 attempt fails because:

1. ✗ **Algorithm correctness depends on unproven Conjecture 1**
2. ✗ **Conjecture 1 is stated but never proven**
3. ✗ **Empirical testing cannot replace mathematical proof**
4. ✗ **Circular reasoning in the argument structure**
5. ✗ **Complexity analysis assumes unverified properties**

**Result**: The claim that P = NP is **NOT established**.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Original paper content
- [`../proof/README.md`](../proof/README.md) - Forward formalization attempt
