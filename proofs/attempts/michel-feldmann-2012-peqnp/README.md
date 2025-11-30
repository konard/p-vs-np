# Michel Feldmann (2012) - P=NP Claim

**Attempt ID**: 86
**Author**: Michel Feldmann
**Year**: 2012 (revised 2020)
**Claim**: P=NP
**Paper**: "Solving satisfiability by Bayesian inference"
**arXiv**: [1205.6658v5](http://arxiv.org/abs/1205.6658)

## Summary

Michel Feldmann claims to prove P=NP by using Bayesian inference to solve the 3-SAT problem in polynomial time. The approach converts Boolean satisfiability problems into linear programming (LP) problems, arguing that this eliminates the distinction between complexity classes P and NP.

## Main Argument

### The Approach

1. **Probabilistic Encoding**: Convert Boolean formulas into a Kolmogorov probability space where:
   - Variables become probability distributions
   - Each Boolean variable Xi gets a probability P(i) = P(Xi = 1|Λ)
   - Logical constraints become linear equations on probabilities

2. **Linear Programming Formulation**:
   - Translate SAT problems into LP systems with:
     - "Specific equations" from the Boolean constraints
     - "Consistency equations" ensuring probability axioms hold
   - Claims the LP system has polynomial size when the maximum clause size is constant

3. **Feasibility = Satisfiability**:
   - For "strict satisfiability" problems (no auxiliary variables), claims:
     - LP feasibility ⟺ Boolean satisfiability
   - Since LP feasibility can be checked in polynomial time, concludes 3-SAT ∈ P

4. **Conclusion**: Therefore P = NP

## The Critical Error

### Fundamental Flaw: Confusing Computational Models

The proof contains a **fundamental category error** that invalidates the entire argument. Feldmann conflates two completely different computational models:

#### 1. The Error in Proposition 7

**Claim**: "When the prior is just a single Boolean function f compelled to be valid the problem accepts a deterministic solution if and only if the Bayesian LP system Eq. (10) is feasible."

**The Problem**: This creates a circular dependency:
- To construct the LP system, one must enumerate all "working unknowns" (Definition 3)
- Working unknowns include all probability variants from the specific equations
- But determining which variants are needed requires knowing the structure of the formula
- For a general 3-SAT formula with M clauses on N variables, this could require examining exponentially many potential unknowns

**Specifically**: The paper claims (Section 5.3) that the number of working unknowns is O(N) for "non-trivial problems" but provides no algorithm or justification for:
1. How to determine this polynomial bound in polynomial time
2. Which specific unknowns to include without examining all 2^N possible states

#### 2. The Hidden Exponential Complexity

**Section 4.3 and Proposition 6** reveal the core issue:

> "By definition of a problem of strict satisfiability, it is possible to assign any deterministic truth value to all unknowns of one literal. This determines the truth value to all working unknowns and to all states ω of the sample set Ω as well."

This means:
- The proof that "LP feasibility = SAT satisfiability" requires checking **all 2^N truth assignments**
- This is exactly the brute-force approach the paper claims to avoid!
- The "polynomial time" claim assumes we can somehow bypass this step, but no algorithm is provided

#### 3. The LP Formulation Hides the Search Problem

The fundamental issue: **Feldmann doesn't solve the search problem; he reformulates it**

- The LP system is feasible ⟺ the Boolean formula is satisfiable
- BUT: Constructing the correct LP system requires essentially solving the SAT problem first
- The paper provides no polynomial-time algorithm to:
  1. Construct the complete set of working unknowns
  2. Ensure the consistency equations are sufficient
  3. Verify the LP system correctly encodes the Boolean formula

#### 4. The Computational Model Mismatch

**The deepest error**: Feldmann treats "checking LP feasibility" as if it solves the original computational problem, but:

- **Standard complexity theory**: Measures computation on a Turing machine with discrete Boolean operations
- **Feldmann's model**: Assumes access to an oracle that can:
  - Solve LP problems in polynomial time
  - Work with **real numbers** (infinite precision)
  - Somehow construct the right LP problem from the SAT instance

**This is not a valid reduction** because:
1. Real-number computation is not the same as Boolean computation (different computational models)
2. The paper assumes we can represent and manipulate exact real numbers in polynomial time
3. The construction phase (SAT → LP) is not proven to be polynomial-time computable

### Why This Doesn't Work

The key insight: **Feldmann proves that IF you could construct the right LP system in polynomial time, THEN you could check satisfiability in polynomial time. But he never proves the IF part is possible.**

The paper essentially says:
- "Convert SAT to LP" (but doesn't show this is polynomial-time)
- "Check LP feasibility" (assuming exact real arithmetic)
- "Therefore SAT is polynomial-time"

This is analogous to saying:
- "Convert SAT to an oracle query"
- "Oracle answers in O(1)"
- "Therefore SAT is O(1)"

## Specific Technical Issues

### Issue 1: The "Working Unknowns" Construction

**Claim** (Proposition 2): "When the number of layers ℓ_max involved in the specific equations is independent of N, the total number of working unknowns is polynomial in the size of the input data."

**Problem**:
- This counts the size of each unknown (constant due to ℓ_max ≤ 3)
- But doesn't account for how many unknowns must be tracked
- The paper claims "removing duplicates" gives polynomial size
- No algorithm or proof is given for computing this deduplicated set in polynomial time

### Issue 2: Proposition 4's Circular Proof

The proof of Proposition 4 (separability of deterministic distributions) proceeds by induction, but:
- Assumes the LP system is already correctly constructed
- Uses consistency equations that must already be complete
- Doesn't address how to verify these properties without exhaustive search

### Issue 3: The "Search Solution" Section 5.7

The paper admits finding a solution requires:
> "checking the feasibility of N successive LP systems of decreasing dimension"

This suggests:
- N LP feasibility checks (each polynomial)
- But each check requires reconstructing the LP system
- The total complexity is hidden in the reconstruction cost

### Issue 4: Real Numbers vs. Discrete Computation

The Bayesian framework requires:
- Exact real-number arithmetic
- Continuous probability distributions
- Convex optimization in real space

But:
- Turing machines compute with discrete symbols
- Real numbers require infinite precision or approximation
- Approximation errors could cause incorrect satisfiability answers

## Formal Verification Goals

Our formalization will explicitly expose these gaps by:

1. **Formalizing the LP construction algorithm**: Show that constructing the LP system from a 3-SAT instance requires examining all satisfying assignments (or equivalent exponential work)

2. **Separating computational models**: Distinguish between:
   - Boolean computation (standard complexity theory)
   - Real arithmetic computation (Feldmann's assumption)
   - Show these are not equivalent

3. **Making hidden complexity explicit**: Track the actual computational cost of:
   - Constructing working unknowns
   - Building consistency equations
   - Verifying the LP correctly encodes the SAT problem

## Formalization Strategy

### Coq Formalization
- Define SAT problems and LP systems formally
- Attempt to formalize the construction algorithm (will expose exponential cost)
- Prove that the construction requires examining exponentially many assignments

### Lean Formalization
- Model both discrete (Turing machine) and continuous (real arithmetic) computation
- Show the computational models are not equivalent
- Formalize the gap between "LP feasibility" and "polynomial-time construction"

### Isabelle Formalization
- Encode the propositions from the paper
- Show Proposition 7's dependency on unproven polynomial-time construction
- Prove the circularity in the argument

## Related Work

This type of error is common in P vs NP attempts:
- Confusing problem representation with problem solution
- Assuming access to non-standard computational models
- Moving exponential complexity into the "setup" phase

## References

1. Feldmann, M. (2020). "Solving satisfiability by Bayesian inference." arXiv:1205.6658v5
2. Cook, S. (1971). "The complexity of theorem proving procedures." STOC 1971.
3. Karp, R. (1972). "Reducibility among combinatorial problems."
4. Woeginger, G. "[The P-versus-NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)" - Entry #86

## Status

- [x] Folder structure created
- [x] Paper analyzed
- [x] README.md created
- [ ] Coq formalization
- [ ] Lean formalization
- [ ] Isabelle formalization

---

**Last Updated**: 2025-10-26
**Formalization Status**: In Progress
