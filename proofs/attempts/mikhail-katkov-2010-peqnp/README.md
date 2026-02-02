# Mikhail Katkov (2010) - P=NP Attempt

**Attempt ID**: 64 (from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm))
**Author**: Mikhail Katkov
**Year**: 2010 (July-August)
**Claim**: P = NP
**Paper**: [arXiv:1007.4257v2](http://arxiv.org/abs/1007.4257) - "Polynomial complexity algorithm for Max-Cut problem"
**Status**: **WITHDRAWN** by author on April 4, 2011

---

## Summary

In July 2010, Mikhail Katkov claimed to prove P=NP by constructing a polynomial-time algorithm for the NP-complete Max-Cut problem. The approach attempted to solve the binary quadratic program formulation of Max-Cut using semi-definite programming on a sum-of-squares polynomial relaxation. The author withdrew the paper in April 2011, acknowledging fundamental flaws in the work.

## Author's Withdrawal

On **April 4, 2011**, Katkov withdrew the paper with this candid statement:

> "The community convinced me that this peace of crank was written by crackpot trisector. I apologize for disturbing community."

This self-deprecating withdrawal confirms the proof contained fundamental flaws that could not be repaired.

## Main Approach

### The Core Idea

1. **Reduce Max-Cut to BQP**: Formulate Max-Cut as a binary quadratic program: minimize x^T Q x subject to xᵢ² = 1
2. **Relax Constraints**: Introduce quartic polynomial Q(α, x) = α x^T Q x + Σᵢ(xᵢ² - 1)²
3. **Sum-of-Squares**: Express Q(α, x) as (or approximate by) a sum of squares
4. **SDP Solution**: Use semidefinite programming to find global minimum in polynomial time
5. **Extract Binary Solution**: Extract binary solution via sign pattern of continuous solution
6. **Claim Optimality**: Assert that for sufficiently small α, sign pattern preserves optimality

### Theorem 4.2 (The Key Claim)

The crucial claim was:

> There exists α* > 0 such that for all 0 ≤ α < α*, the sign pattern of the global minimum x*(α) matches the sign pattern of the global minimum x*(0).

**Why this would prove P=NP:**
- At α = 0, global minima satisfy xᵢ² = 1 (binary constraint)
- For small α > 0, SDP can find global minimum in polynomial time
- If sign pattern is preserved, binary solution solves Max-Cut
- Since Max-Cut is NP-complete, this would prove P=NP

## The Six Critical Errors

### 1. Theorem 4.2 NOT PROVEN for Global Minima

**What the paper proves:**
- LOCAL perturbation analysis near feasible points
- Shows that small changes near points with xᵢ² = 1 preserve sign patterns

**What the paper needs but does NOT prove:**
- GLOBAL minimum preserves sign pattern as α → 0
- No proof that global minimum doesn't jump to different solution branch
- No analysis of bifurcations

**The gap:** Local property ≠ Global property

### 2. Uniqueness NOT ESTABLISHED

**The assumption:**
> For sufficiently small α, the global minimum is unique.

**The reality:**
- Many graphs have multiple optimal cuts with equal weight
- These lead to multiple global minima
- As α → 0, solutions can form continuous manifolds
- Uniqueness is assumed but never proven

**Example:** Complete graph K₄ with unit weights has three different optimal 2-2 partitions.

### 3. Gap Δ Can Be Zero

**Equation (24) assumes:**
```
Δ > αn(λ²_max/2 - λ²_min/4) + o(α)
```
where Δ is "the minimum difference between cuts."

**The problem:**
- Requires Δ > 0
- Many graphs have Δ = 0 (multiple cuts with same weight)
- When Δ = 0, inequality fails for any α > 0
- Symmetric graphs, complete graphs, bipartite graphs all have Δ = 0

### 4. Bifurcations Are Possible

**The assumption:**
> As α varies, the global minimum varies continuously.

**The reality:**
- Non-convex optimization can have bifurcations
- Global minimum can jump discontinuously between branches
- Sign pattern can change as α varies
- No proof prevents this

### 5. Certificate Extraction Is Heuristic

**The claim (Section 5):**
> Extract binary solution via sign of continuous solution: xᵢ = sign(xᵢ*)

**The problem:**
- Not rigorously proven
- Ambiguous when xᵢ* ≈ 0
- Rounding continuous to binary is THE hard part of Max-Cut
- Goemans-Williamson (1995) proved integrality gap exists

### 6. No Complexity Analysis for α*

**Missing:**
> How to compute α* such that claimed properties hold?

**The problem:**
- If α* is exponentially small (e.g., 2⁻ⁿ), then:
  - Finding α* requires exponential precision
  - Numerical computations need exponential bits
  - Polynomial-time claim fails

## Why This Matters: The Local vs. Global Gap

The fundamental error is conflating **local properties** with **global properties**:

```
✓ PROVEN (Local):
  Near a feasible point x₀ with xᵢ² = 1,
  small perturbations preserve sign patterns

✗ NOT PROVEN (Global):
  The global minimum x*(α) preserves
  sign pattern as α → 0
```

This gap is fatal because:
- Non-convex optimization has multiple local minima
- Global minimum can jump between solution branches
- Bifurcations cause discontinuous behavior
- Local stability doesn't guarantee global stability

## Related Work and Context

### Why SDP Doesn't Solve NP-Hard Problems

**Goemans-Williamson (1995):**
- Proved SDP gives 0.878-approximation for Max-Cut
- Proved integrality gap exists
- Showed continuous ≠ discrete optimum

**The barrier:**
- SDP solves continuous relaxation in polynomial time ✓
- But rounding to discrete solution is NP-hard ✗
- Katkov's sign extraction assumes rounding is free (incorrect)

### Historical Significance

- **Woeginger's List Entry:** #64
- **Withdrawal:** One of the few with candid acknowledgment
- **Educational Value:** Demonstrates common pitfalls in continuous relaxation approaches

## Directory Structure

```
proofs/attempts/mikhail-katkov-2010-peqnp/
├── README.md                       # This file
├── ORIGINAL.md                     # Markdown conversion of paper
├── ORIGINAL.pdf                    # Original paper (arXiv:1007.4257v2)
├── proof/
│   ├── README.md                   # Forward proof formalization guide
│   ├── lean/KatkovProof.lean       # Lean 4 proof attempt
│   └── rocq/KatkovProof.v          # Rocq proof attempt
├── refutation/
│   ├── README.md                   # Detailed error analysis
│   ├── lean/KatkovRefutation.lean  # Lean 4 refutation
│   └── rocq/KatkovRefutation.v     # Rocq refutation
└── archive/
    └── isabelle/                   # Archived Isabelle formalization
```

## Verification Status

- ✅ Original paper documented (ORIGINAL.md, ORIGINAL.pdf)
- ✅ Proof attempt formalized (proof/lean/KatkovProof.lean, proof/rocq/KatkovProof.v)
- ✅ Refutation formalized (refutation/lean/KatkovRefutation.lean, refutation/rocq/KatkovRefutation.v)
- ✅ All six errors identified and documented
- ✅ Author's withdrawal statement preserved
- ✅ Isabelle formalization archived (support sunset)

## Key Lessons

This attempt demonstrates common pitfalls in P vs NP proofs:

1. **Local ≠ Global**: Local analysis doesn't imply global properties
2. **Uniqueness Matters**: Multiple optimal solutions break many arguments
3. **Degeneracies Are Common**: Equal-weight solutions occur frequently
4. **Continuous ≠ Discrete**: Relaxation introduces integrality gaps
5. **SDP Is Not Magic**: Polynomial-time continuous optimization ≠ discrete optimization
6. **Proof Details Matter**: "For sufficiently small α" requires proving α* exists and is computable

## See Also

- **Original Paper**: [arXiv:1007.4257v2](https://arxiv.org/abs/1007.4257)
- **Woeginger's List**: [Entry #64](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
- **Goemans-Williamson (1995)**: "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming"
- **Parrilo (2003)**: "Semidefinite programming relaxations for semialgebraic problems"

---

**Formalization Status**: Complete ✓
**Errors Identified**: 6
**Withdrawal**: Confirmed by author
**Educational Value**: High (demonstrates local vs. global gap)
