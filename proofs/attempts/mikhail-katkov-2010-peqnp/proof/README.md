# Forward Proof Formalization: Katkov 2010

This directory contains the formal proof attempt following Katkov's approach as faithfully as possible.

## Contents

- `lean/KatkovProof.lean` - Lean 4 formalization
- `rocq/KatkovProof.v` - Rocq (Coq) formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **Max-Cut Problem Definition**: Weighted graph and cut weight computation
2. **Binary Quadratic Program (BQP)**: Standard reduction from Max-Cut to BQP
3. **Katkov's Quartic Relaxation**: Q(α, x) = α x^T Q x + Σᵢ(xᵢ² - 1)²
4. **Sum-of-Squares (SOS) Framework**: Polynomial SOS representation and SDP relaxation
5. **Theorem 4.2 (Sign Preservation Claim)**: The crucial claimed result
6. **Uniqueness Claim**: Assumption that global minimum is unique for small α
7. **Polynomial Time Claim**: SDP solvability assertion

## The Attempted Proof Logic

Katkov's argument proceeds:

1. **Reduce Max-Cut to BQP**: Formulate as minimize x^T Q x subject to xᵢ² = 1
2. **Relax Constraints**: Replace hard constraint with penalty: Q(α, x) = α x^T Q x + Σᵢ(xᵢ² - 1)²
3. **Express as SOS**: Show Q(α, x) is (or approximates) a sum of squares
4. **Solve via SDP**: Use semidefinite programming to find global minimum in polynomial time
5. **Extract Binary Solution**: Claim sign pattern of continuous solution gives binary solution
6. **Preserve Optimality**: Assert that for sufficiently small α, the sign pattern matches optimal cut
7. **Conclude P=NP**: Since Max-Cut is NP-complete and we solved it in polynomial time

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Katkov's argument fails. These mark locations where:

1. **Theorem 4.2 (Sign Preservation)**: The paper analyzes local perturbations but does NOT prove this holds for GLOBAL minima
2. **Uniqueness Assumption**: The claim that global minimum is unique is assumed but not proven
3. **Zero Gap Problem**: Equation (24) assumes Δ > 0 but Δ = 0 for graphs with multiple optimal cuts
4. **Bifurcation Analysis**: No proof that sign pattern is continuous as α varies
5. **Certificate Extraction**: The eigenvector method is presented as heuristic, not rigorously proven
6. **Alpha Complexity**: No analysis of how small α* must be (if exponentially small, precision requirements explode)

## The Core Error

The proof rests on **Theorem 4.2** which claims:

> There exists α* > 0 such that for all 0 ≤ α < α*, the sign pattern of global minimum x*(α) matches the sign pattern of global minimum x*(0).

**What the paper proves:**
- For small perturbations near a feasible point (where xᵢ² = 1), the sign is locally preserved
- This is a LOCAL analysis around specific solution points

**What the paper needs but does NOT prove:**
- The GLOBAL minimum of Q(α, x) preserves the sign pattern
- This requires proving the global minimum doesn't jump to a different solution branch
- Bifurcations can occur as α changes, causing discontinuous sign changes

### The Gap Between Local and Global

```
Local property (proven):
  At a point x₀ with xᵢ² = 1, small perturbations preserve sign

Global property (needed but NOT proven):
  The global minimum x*(α) has the same sign pattern as x*(0)
```

The gap: local analysis ≠ global guarantees

## Mathematical Details

### The Relaxation Function

For binary vector x ∈ {-1, +1}ⁿ with xᵢ² = 1:
- Original: minimize x^T Q x
- At α = 0: Q(0, x) = Σᵢ(xᵢ² - 1)² = 0 exactly when xᵢ² = 1
- For α > 0: Q(α, x) = α x^T Q x + Σᵢ(xᵢ² - 1)²

### The Claimed Continuity

The paper claims that as α → 0⁺, the global minimum x*(α) continuously approaches some x*(0) with xᵢ² = 1, preserving sign patterns.

**Problem:** This requires:
1. Uniqueness of x*(α) for each α
2. Continuity of x*(α) as function of α
3. No bifurcations where solutions split or merge

None of these are proven in the paper.

### Equation 24 and the Zero Gap Issue

The paper's equation (24) states:
```
Δ > αn(λ²_max/2 - λ²_min/4) + o(α)
```

where Δ is "the minimum difference between cuts."

**Fatal flaw:**
- If two cuts have equal weight, then Δ = 0
- The inequality cannot hold for any α > 0
- Many graphs have multiple optimal cuts with identical weights
- Examples: complete graphs, symmetric graphs, bipartite graphs

## Why SDP Doesn't Solve This

While SDP can solve many optimization problems, it doesn't automatically solve NP-hard problems:

1. **Goemans-Williamson (1995)**: Proved SDP gives 0.878-approximation for Max-Cut
2. **Integrality Gap**: Continuous SDP solution ≠ binary optimal solution
3. **Rounding Required**: Getting binary solution from continuous solution is the hard part
4. **Katkov's Assumption**: Claims sign extraction works perfectly, but this is unproven

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Original paper summary
- [`../refutation/README.md`](../refutation/README.md) - Why the proof fails
