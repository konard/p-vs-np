# Refutation: Why Akbari's Claim Fails

This directory contains formalizations showing why clique-based P = NP attempts typically fail.

## Contents

- `lean/AkbariAttempt.lean` - Lean 4 formalization of failure modes
- `rocq/AkbariAttempt.v` - Rocq formalization of failure modes

## What the Refutation Demonstrates

While Akbari's logical implication is correct (polynomial-time clique algorithm → P = NP), the claim fails because the premise is unsubstantiated. These formalizations show:

1. **Common Failure Modes** in clique-based P = NP attempts
2. **Why these approaches fail** to prove the required claims
3. **What would actually be needed** for a valid proof

## Failure Modes Formalized

### 1. Partial Algorithms (Special Cases Only)

**Problem**: Many proposed algorithms work efficiently on specific graph structures but fail on general graphs.

**Formalization**: Shows that an algorithm working on some graphs doesn't satisfy the requirement ∀G (algorithm solves G correctly).

**Why it fails**: NP-completeness requires worst-case polynomial time over ALL instances, not just special cases.

### 2. Hidden Exponential Complexity

**Problem**: The algorithm appears polynomial when expressed in terms of certain parameters, but those parameters can be exponential in the input size.

**Example**:
- Runtime appears to be O(n × C(G)) where C(G) is "number of cliques in G"
- But C(G) can be 2^n for n vertices
- Actual complexity: O(n × 2^n) = exponential

**Formalization**: Demonstrates algorithms with apparent polynomial complexity that are actually exponential.

### 3. Clique Enumeration Approaches

**Problem**: Algorithms bounded by the number of cliques in a graph.

**Why it fails**:
- A complete graph K_n has 2^n cliques
- Any algorithm that must examine all cliques runs in exponential time

**Formalization**: Proves that clique-enumeration-based algorithms have exponential worst-case time.

### 4. Membership-Bounded Algorithms

**Problem**: Algorithms bounded by the number of cliques each vertex belongs to.

**Why it fails**:
- In a complete graph K_n, each vertex belongs to 2^(n-1) cliques
- Runtime becomes exponential

**Formalization**: Shows that membership-bounded approaches lead to exponential time.

## The Core Issue

All of these failure modes share a common pattern:

1. ✅ **Correct observation**: Clique is NP-complete
2. ✅ **Correct logic**: Polynomial algorithm for clique → P = NP
3. ❌ **Unproven claim**: A polynomial-time algorithm exists
4. ❌ **Hidden complexity**: Parameters that appear polynomial are actually exponential

## What a Valid Proof Would Require

For Akbari's approach to work, the following would need to be proven:

1. **Complete Specification**: A precise, unambiguous description of the algorithm
2. **Polynomial Time Bound**: Proof that the algorithm runs in O(n^k) time for some constant k, where n is the input size
3. **Universal Correctness**: Proof that the algorithm correctly solves the clique problem for EVERY possible graph
4. **Worst-Case Analysis**: The polynomial bound must hold in the worst case, not just average case

## Key Insights from the Refutation

### The Exponential Gap

The number of potential cliques in a graph grows exponentially:
- n vertices can form up to 2^n possible cliques
- Checking all possibilities takes exponential time
- Any polynomial algorithm must avoid exhaustive enumeration

### The Universal Quantifier Requirement

A valid proof requires:
- **What's needed**: ∀G (algorithm solves G in polynomial time)
- **What failed attempts show**: ∃G₁, G₂, ... (algorithm solves these specific graphs)

The difference between ∀ (for all) and ∃ (there exists) is crucial.

### NP-Completeness is a Barrier

If any polynomial-time algorithm for an NP-complete problem existed:
- It would be revolutionary
- It would prove P = NP
- It would contradict decades of computational complexity theory
- It would have been independently verified and widely accepted

The absence of such verification suggests the algorithm doesn't work as claimed.

## Historical Context

Similar clique-based P = NP attempts have failed:

1. **Hamelin (2011)**: Complexity hidden in clique membership bounds
2. **Dhami et al. (2014)**: Withdrawn after failure on large instances
3. **Cardenas et al. (2015)**: Provided systematic refutations

These historical failures follow the same patterns formalized here.

## Conclusion

The refutation doesn't show that P ≠ NP (that remains open). Instead, it shows:

1. Akbari's specific approach doesn't provide the required proofs
2. Common pitfalls in clique-based P = NP attempts
3. Why such attempts typically fail
4. What would actually be needed for success

The formalization serves an educational purpose: understanding why proof attempts fail helps build intuition about the P vs NP problem and the challenges involved in resolving it.
