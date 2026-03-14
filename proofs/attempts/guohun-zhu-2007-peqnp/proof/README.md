# Forward Proof Attempt - Guohun Zhu (2007)

This directory contains an attempt to formalize the forward direction of Guohun Zhu's 2007 proof attempt that claims P=NP.

## Status

**Incomplete**: The forward proof formalization is incomplete because the original paper contains fundamental errors that prevent completing a valid proof.

## Why the Forward Proof Cannot Be Completed

The original paper claims to solve the Hamiltonian Cycle Problem (HCP) in polynomial time for directed graphs with degree bound two. The approach involves:

1. **Projector Graph Construction** (Theorem 1): Mapping a Γ-digraph to a balanced bipartite graph
2. **Perfect Matching Correspondence** (Theorem 2): Showing Hamiltonian cycles correspond to perfect matchings with a rank condition
3. **Polynomial-Time Algorithm** (Theorem 3): Claiming there are only O(n) matchings to check

## The Critical Gap

**Lemma 4 (page 7)** contains the fatal error: The paper claims there are only n/2 non-isomorphic perfect matchings to enumerate, when in fact there are **2^(n/4)** matchings (exponential).

This makes it impossible to complete the forward proof because:
- No polynomial-time enumeration algorithm is provided
- The claimed linear bound on matchings is mathematically incorrect
- The "isomorphism" argument doesn't reduce exponential to linear complexity

## Formalization Approach

To formalize what can be formalized:
1. Define Γ-digraphs and projector graphs
2. Formalize the bijection between matchings and cycles (Theorems 1-2)
3. **Cannot formalize**: The polynomial-time enumeration claim (requires fixing the exponential explosion)

## Why This Matters

This incomplete forward proof demonstrates that **the original approach cannot work as stated**. Any attempt to complete it must resolve the exponential counting problem, which would require a fundamentally different algorithm.

---

*See `../refutation/` for the formal refutation of this attempt.*
