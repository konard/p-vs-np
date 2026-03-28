# Refutation: Gubin 2010

This directory contains formalizations that demonstrate the critical errors in Sergey Gubin's 2010 attempted proof of P = NP via ATSP polytope formulation.

## Contents

- `lean/GubinRefutation.lean` - Lean 4 formalization of the refutation
- `rocq/GubinRefutation.v` - Rocq (Coq) formalization of the refutation

## Summary of Errors

Gubin's proof fails due to **fundamental flaws**:

1. **Missing Proof of Integrality** (Fatal)
2. **The LP/ILP Gap** (Fundamental barrier)
3. **Asymmetry Does Not Imply Integrality** (Logical gap)
4. **Rizzi's Refutation** (Explicit counter-example)

## Error 1: Missing Proof of Integrality

### The Critical Missing Step

Gubin's argument requires proving:
- All extreme points (vertices) of the LP polytope have integral (integer) coordinates
- These integral extreme points correspond exactly to valid ATSP tours

**This is never proven. It is merely assumed.**

### Why This Matters

Without integrality:
- The LP optimal solution may be fractional (e.g., "use edge (i,j) 0.5 times")
- Fractional solutions do not correspond to valid tours
- Rounding fractional solutions is NP-hard in general
- The correspondence between LP and ATSP breaks down

### The Formalization

The refutation formalizes the gap between:
- `HasIntegralCorrespondence`: The claimed property (tours ↔ integral extreme points)
- `gubin_lacks_integrality_proof`: This property is not proven

## Error 2: The LP/ILP Gap

### The Fundamental Barrier

| Property | Linear Programming (LP) | Integer Linear Programming (ILP) |
|----------|------------------------|----------------------------------|
| Variables | Real numbers | Integers only |
| Solvability | Polynomial time | NP-complete |
| Extreme Points | May be fractional | Always integral |

### Why This Gap Is Decisive

The LP/ILP gap means:
- Solving LP does not solve ILP
- LP solutions may need "rounding" to become integer
- Rounding correctly is generally NP-hard
- The gap is precisely where combinatorial hardness lives

### The Formalization

The refutation formalizes:
- `LP_solvable_in_polynomial_time`: LP is in P
- `ILP_is_NP_complete`: ILP is NP-complete
- `LP_ILP_gap`: The fundamental distinction between continuous and discrete optimization

## Error 3: Asymmetry Does Not Imply Integrality

### The Logical Gap

Gubin claims his formulation is "complementary to Yannakakis' theorem" because:
- Yannakakis: Symmetric formulations require exponential size
- Gubin: Uses an asymmetric formulation of polynomial size

**But avoiding Yannakakis does not prove integrality!**

### What Asymmetry Provides

Being asymmetric means:
- The formulation is not invariant under variable permutation
- Yannakakis' lower bound does not directly apply
- The formulation can have polynomial size

### What Asymmetry Does NOT Provide

Being asymmetric does NOT imply:
- Extreme points are integral
- Extreme points correspond to tours
- The LP optimal equals the ATSP optimal
- The formulation correctly captures ATSP

### The Formalization

The refutation proves:
- `asymmetry_insufficient`: Asymmetry alone cannot establish integrality
- `yannakakis_not_only_barrier`: Avoiding Yannakakis is necessary but not sufficient

## Error 4: Rizzi's Refutation (2011)

### The Historical Refutation

In January 2011, Romeo Rizzi published a refutation of Gubin's arguments:
- Documented in Woeginger's P vs NP page
- Demonstrates that the correspondence claim is false

### The Pattern of Refutation

Like other LP-based P=NP attempts, the refutation likely shows:
- Specific instances where LP extreme points are fractional
- Cases where LP optimal differs from ATSP optimal
- Counter-examples to the correspondence claim

### The Formalization

The refutation includes:
- `rizzi_refutation_2011`: Axiom representing the historical refutation
- `gubin_correspondence_is_false`: The integrality correspondence is proven false

## Key Lessons

### 1. Polynomial Size ≠ Correctness

Having a polynomial-sized formulation does not mean:
- The formulation captures the problem correctly
- Solutions to the formulation correspond to problem solutions
- The problem is efficiently solvable

### 2. Avoiding Known Barriers ≠ Success

Circumventing Yannakakis' symmetric barrier:
- Is necessary for a polynomial-sized LP approach
- Is NOT sufficient for proving P = NP
- Does not address the integrality problem

### 3. Claims Require Proofs

Structural claims about polytopes require rigorous proof:
- Integrality must be proven, not assumed
- Correspondence must be established formally
- Hand-waving about "complementary" relationships is insufficient

### 4. The LP/ILP Gap Is Fundamental

The gap between continuous and discrete optimization:
- Is well-understood in complexity theory
- Cannot be bridged by clever formulations alone
- Is precisely where NP-hardness resides

## Similar Attempts

### Moustapha Diaby (2004)

- Claimed polynomial-sized LP formulation for TSP (symmetric case)
- Refuted by Hofman (2006, 2025) with explicit counter-examples
- Same fundamental issue: integrality not proven

### General Pattern

1. Construct polynomial-sized LP/optimization formulation
2. Claim it captures the combinatorial structure
3. Infer P = NP from efficient solvability
4. Fail to prove the crucial structural property
5. Get refuted by counter-examples

## What Would Be Required for a Valid Proof

To validly prove P = NP via this approach, one would need:

### 1. Rigorous Integrality Proof

Prove that ALL extreme points of the LP polytope are integral. This requires:
- Characterizing the polytope structure
- Proving no fractional vertices exist
- Using techniques from polyhedral combinatorics

### 2. Exact Correspondence

Prove a bijection between:
- Integral extreme points of the LP polytope
- Valid ATSP tours

### 3. Objective Preservation

Prove that the LP objective value equals the ATSP tour cost at extreme points.

### 4. Handle All Cases

The proof must work for ALL directed graphs, not just specific examples.

## Conclusion

Gubin's proof fails because it assumes the integrality/correspondence property without proof. This is the same failure mode as many other LP-based P = NP attempts. The LP/ILP gap is a fundamental barrier that cannot be bypassed by simply avoiding Yannakakis' theorem.

Rizzi's 2011 refutation confirms that the correspondence claim is false, definitively closing this approach.

## See Also

- [`../README.md`](../README.md) - Complete overview and error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../proof/README.md`](../proof/README.md) - Forward formalization showing what Gubin actually proves
