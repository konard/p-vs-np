# Refutation of Guohun Zhu's 2007 P=NP Attempt

This directory contains formal refutations of Guohun Zhu's 2007 claim that P=NP.

## The Error

**Location**: Lemma 4, page 7 of the original paper

**The Claim**: "The maximal number of unlabeled perfect matchings in a projector graph G is n/2."

**Why It's Wrong**: With k independent components (where k ≤ n/4), each having 2 perfect matching choices, the number of distinct matchings is **2^k**, not 2k.

## Formal Refutations

### Lean (refutation/lean/ZhuRefutation.lean)

Proves:
- `correct_matching_count`: For k ≥ 2, we have 2^k > 2k
- `exponential_vs_linear`: For n ≥ 12, we have 2^(n/4) > n/2
- `zhu_lemma_4_is_false`: The claimed linear bound contradicts exponential growth

### Rocq/Coq (refutation/rocq/ZhuRefutation.v)

Proves:
- The exponential growth property using the `lia` tactic
- Counterexamples showing 2^k ≠ 2k for k ≥ 2
- The impossibility of enumerating exponentially many matchings in polynomial time

## Mathematical Explanation

### The Counting Error

If a projector graph has k components (where k ≤ n/4), and each component has 2 perfect matching choices:

- **Zhu's claim**: 2 + 2 + ... + 2 (k times) = 2k matchings (LINEAR)
- **Correct**: 2 × 2 × ... × 2 (k times) = 2^k matchings (EXPONENTIAL)

### Concrete Example

For n = 12 (so k = 3):
- **Zhu's claim**: 2×3 = 6 matchings
- **Actual**: 2^3 = 8 matchings

For n = 16 (so k = 4):
- **Zhu's claim**: 2×4 = 8 matchings
- **Actual**: 2^4 = 16 matchings

As k grows, 2^k grows exponentially while 2k grows linearly. This exponential explosion destroys the polynomial-time claim.

## Additional Issues

1. **No enumeration algorithm**: The paper provides recursive equations (10-11) but no proof they enumerate all matchings
2. **Isomorphism confusion**: The "isomorphism" argument doesn't reduce the exponential count
3. **Missing rank check**: No polynomial-time algorithm is given to systematically check the rank condition for all matchings

## Conclusion

The refutation shows that Zhu's approach **cannot** solve HCP in polynomial time because:
1. The number of matchings to check is exponential, not linear
2. No polynomial-time enumeration method exists for all such matchings
3. The fundamental counting argument (Lemma 4) is mathematically incorrect

This is a common error in P vs NP attempts: **confusing linear growth with exponential growth** in combinatorial counting.

---

*See `../proof/` for discussion of what parts of the forward proof can be formalized.*
