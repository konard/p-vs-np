# Mikhail Katkov (2010) - Refutation

## Why the Proof Fails

Katkov's 2010 P=NP attempt contains multiple fundamental errors. The paper was **withdrawn by the author** on April 4, 2011.

## Author's Withdrawal

From arXiv (April 4, 2011):

> "The community convinced me that this peace of crank was written by crackpot trisector. I apologize for disturbing community."

While self-deprecating, this withdrawal confirms the proof's fundamental flaws.

## The Six Critical Errors

### Error 1: Theorem 4.2 (Sign Preservation) Is NOT PROVEN

**The Claim (pages 3-4):**
> There exists α* > 0 such that for all 0 ≤ α < α*, the sign pattern of global minimum x*(α) matches the sign pattern of global minimum x*(0).

**What the Paper Actually Proves:**
- Local perturbation analysis near feasible points (where xᵢ² = 1)
- Shows that LOCALLY, small changes preserve sign patterns

**What's Missing:**
- Proof that this holds for GLOBAL minima
- Proof that global minimum doesn't jump to different solution branch
- Analysis of bifurcations as α varies

**Why This Matters:**
- Local property ≠ global property
- Global minimum can discontinuously jump between solution branches
- Bifurcations can cause sign flips even if local analysis is stable

### Error 2: Uniqueness Is NOT ESTABLISHED

**The Claim (implicit in Section 4):**
> For sufficiently small α, the global minimum is unique.

**The Reality:**
- Many graphs have multiple optimal cuts with equal weight
- These lead to multiple global minima
- As α → 0, solutions can form continuous manifolds
- Uniqueness is assumed but never proven

**Counterexample:**
Complete graph K₄ with all edges weight 1:
- Multiple cuts have weight 3 (optimal)
- Relaxed problem has multiple global minima
- Uniqueness fails

### Error 3: Gap Δ Can Be Zero

**The Claim (Equation 24, page 6):**
```
Δ > αn(λ²_max/2 - λ²_min/4) + o(α)
```
where Δ is "the minimum difference between cuts."

**The Problem:**
- Assumes Δ > 0 (positive gap between distinct cut values)
- Many graphs have Δ = 0 (multiple cuts with same weight)
- Inequality cannot hold when Δ = 0

**Examples with Δ = 0:**
- Complete graphs (symmetric cuts have equal weight)
- Bipartite graphs (perfect partitions have equal weight)
- Any graph with symmetry

**Consequence:**
When Δ = 0, equation (24) fails, and the uniqueness argument collapses.

### Error 4: Bifurcations Are Possible

**The Assumption:**
> As α varies from α to 0, the global minimum x*(α) varies continuously.

**The Reality:**
- Non-convex optimization can have bifurcations
- Global minimum can jump discontinuously
- Sign pattern can change as α varies
- No proof prevents this

**What Happens at Bifurcations:**
```
For α = 0.001: x*(α) = [+1, +1, -1, -1] (one solution branch)
For α = 0.0001: x*(α) = [+1, -1, +1, -1] (different branch)
                         ↑    ↑
                    Sign flips occurred!
```

### Error 5: Certificate Extraction Is Heuristic

**The Claim (Section 5):**
> Extract binary solution via sign of eigenvector components: xᵢ = sign(xᵢ*)

**The Problem:**
- Not rigorously proven
- Works for some cases, fails for others
- When continuous solution is near zero (xᵢ* ≈ 0), sign is ambiguous
- Rounding continuous to binary is THE hard part of Max-Cut

**Known Result (Goemans-Williamson 1995):**
- Proved SDP gives 0.878-approximation for Max-Cut
- Proved integrality gap exists
- Proved you cannot always extract exact solution

### Error 6: No Complexity Analysis for α

**The Missing Piece:**
> How to compute α* such that the claimed properties hold?

**The Problem:**
- If α* is exponentially small, finding it requires exponential precision
- Numerical precision requirements could be exponential in n
- Polynomial-time claim is incomplete without this analysis

**Concrete Issue:**
- Paper claims "sufficiently small α"
- But if α* = 2⁻ⁿ, then:
  - Representing α* requires n bits
  - Numerical computations need exponential precision
  - "Polynomial time" claim fails

## The Fundamental Barrier: Local vs. Global

The core error is conflating **local properties** with **global properties**:

| Aspect | Local Analysis | Global Guarantee |
|--------|---------------|------------------|
| **What's proven** | Near feasible point x₀, small perturbations preserve sign | ❌ Not proven |
| **What's needed** | Global minimum x*(α) preserves sign pattern as α → 0 | ❌ Not proven |
| **The gap** | Local stability ≠ Global stability | ❌ Fatal |

## Why SDP Doesn't Magically Solve NP-Hard Problems

**Common Misconception:**
> "SDP is polynomial time, so using SDP to solve Max-Cut gives P=NP!"

**Reality:**
1. **SDP Solves Continuous Relaxation**: Finds optimal continuous solution, not binary solution
2. **Integrality Gap Exists**: Continuous optimum ≠ discrete optimum
3. **Rounding Is Hard**: Converting continuous to binary solution is NP-hard itself
4. **Approximation, Not Exact**: Goemans-Williamson proved 0.878-approximation, not exact solution

## Concrete Counterexample

Consider the complete graph K₄ with all edges weight 1:

**Optimal Binary Solutions** (multiple exist):
- S = {1, 2}, T = {3, 4} → cut weight = 4
- S = {1, 3}, T = {2, 4} → cut weight = 4
- S = {1, 4}, T = {2, 3} → cut weight = 4

**Consequence:**
- Multiple optimal cuts with equal weight (Δ = 0)
- Relaxed problem has multiple global minima
- Uniqueness fails
- Equation (24) fails
- Theorem 4.2 cannot hold

## Mathematical Proof of Failure

### Theorem (Zero Gap Exists)

**Statement:** There exist graphs with Δ = 0 (multiple optimal cuts with equal weight).

**Proof:**
- Consider K₄ (complete graph on 4 vertices) with unit edge weights
- Any 2-2 partition gives cut weight 4
- There are 3 such partitions: {1,2},{3,4}, {1,3},{2,4}, {1,4},{2,3}
- All have equal weight → Δ = 0 ∎

### Theorem (Equation 24 Fails)

**Statement:** When Δ = 0, equation (24) cannot hold.

**Proof:**
- Equation (24): Δ > αn(λ²_max/2 - λ²_min/4) + o(α)
- When Δ = 0: 0 > αn(λ²_max/2 - λ²_min/4) + o(α)
- For α > 0 and n > 0, RHS > 0
- Contradiction: 0 > (positive number)
- Therefore equation (24) fails when Δ = 0 ∎

### Theorem (Katkov's Approach Cannot Work)

**Statement:** Sign preservation (Theorem 4.2) cannot hold for all graphs.

**Proof:**
- For graphs with Δ = 0, multiple optimal cuts exist
- Relaxed problem Q(α, x) has multiple global minima
- As α → 0, different minima can be reached
- Sign patterns of different minima differ
- No unique sign pattern is preserved
- Therefore Theorem 4.2 fails for these graphs ∎

## Historical Context and Lessons

### Why This Attempt Failed

1. **Confused Local and Global**: Proved local property, assumed global property
2. **Assumed Uniqueness Without Proof**: Critical for argument, but unproven
3. **Ignored Degeneracies**: Assumed Δ > 0, but Δ = 0 is common
4. **Misunderstood SDP**: SDP solves continuous relaxation, not discrete problem
5. **No Counterexample Analysis**: Didn't check edge cases like symmetric graphs

### Common Pitfalls in P vs NP Attempts

This attempt demonstrates several common errors:

1. **Relaxation Fallacy**: Continuous relaxation ≠ discrete problem
2. **Approximation ≠ Exact**: SDP gives approximation, not exact solution
3. **Local ≠ Global**: Local analysis doesn't imply global properties
4. **Assumed Uniqueness**: Many problems have multiple optimal solutions
5. **Ignored Complexity of Parameters**: Small parameters may require exponential precision

### Related Failed Approaches

Many P=NP attempts use similar flawed logic:
- **Continuous Relaxation**: Try to solve discrete problem via continuous optimization
- **Heuristic Extraction**: Assume rounding gives optimal solution (usually false)
- **Local Analysis**: Prove local properties, assume they're global (usually false)

### Why We Believe P ≠ NP

This attempt illustrates the fundamental barrier:
- Continuous optimization (P) is fundamentally easier than discrete optimization (NP)
- Relaxation introduces integrality gaps that cannot be closed
- No known technique bridges the discrete-continuous gap for NP-hard problems

## Formal Refutations

The formalizations in this directory demonstrate:

1. **`theorem_4_2_not_proven`**: Sign preservation is claimed but not proven
2. **`uniqueness_not_proven`**: Uniqueness assumption is unjustified
3. **`zero_gap_exists`**: Graphs with Δ = 0 exist
4. **`equation_24_fails_when_gap_zero`**: Equation (24) fails for these graphs
5. **`bifurcations_possible`**: Sign pattern can change discontinuously
6. **`paper_withdrawn`**: Author acknowledged the errors

## Key Takeaways

1. **Local Stability ≠ Global Stability**: Perturbation analysis around one point doesn't guarantee global properties
2. **Uniqueness Matters**: Multiple optimal solutions break many arguments
3. **Degeneracies Are Common**: Equal-weight solutions occur frequently
4. **SDP Is Not Magic**: Continuous optimization doesn't automatically solve discrete problems
5. **Proof Details Matter**: Claiming "for sufficiently small α" without proving existence is insufficient

## References

- **Katkov, M.** (2010). "Polynomial complexity algorithm for Max-Cut problem." arXiv:1007.4257v2 [withdrawn]
- **Goemans, M. W., & Williamson, D. P.** (1995). "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming." Journal of the ACM, 42(6), 1115-1145. [Proves integrality gap exists]
- **Parrilo, P. A.** (2003). "Semidefinite programming relaxations for semialgebraic problems." Mathematical Programming, Series B, 96(2), 293-320.
- **Woeginger's List**: Entry #64 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
