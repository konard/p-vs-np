# Michel Feldmann (2012) - Refutation

## Why the Proof Fails

Feldmann's 2012 P=NP attempt contains a fundamental gap: **no polynomial-time algorithm is provided to construct the LP system from a SAT formula**.

## The Fatal Error: Missing Construction Algorithm

### The Claim

Feldmann claims:
1. Any 3-SAT formula can be converted to an LP system of polynomial size (Proposition 2)
2. LP feasibility ↔ Boolean satisfiability (Proposition 7)
3. LP feasibility is polynomial-time (Khachiyan 1979)
4. Therefore 3-SAT ∈ P

### The Problem

The proof is structured as a two-step process:

| Step | Task | Status |
|------|------|--------|
| **Step 1** | Construct LP system C(f) from SAT formula f | ✗ No polynomial algorithm given |
| **Step 2** | Check LP feasibility | ✓ Proven polynomial (Khachiyan 1979) |

Feldmann proves **Step 2** is easy (already known since 1979), but **never proves Step 1 can be done in polynomial time**.

## The Three Unproven Requirements

### Requirement 1: Computing Working Unknowns

**Paper's Claim** (Proposition 2): "When the number of layers ℓ_max involved in the specific equations is independent of N, the total number of working unknowns is polynomial."

**The Gap**: This counts the *size* of each unknown (bounded by ℓ_max ≤ 3) but never:
- Gives an algorithm to enumerate which unknowns to track
- Proves the enumeration takes polynomial time
- Shows that the deduplicated set can be computed without examining exponentially many candidates

### Requirement 2: Building Consistency Equations

The "consistency equations" (Definition 4) depend on the set of working unknowns from Requirement 1. Without a polynomial algorithm for that, consistency equations cannot be built in polynomial time either.

### Requirement 3: Verifying Correctness

**Paper's Proposition 6**: "In a problem of strict satisfiability, the LP system determines the truth table."

**The Gap**: The proof of this proposition says we can check consistency "by force brute" — examining all 2^N truth assignments. This is explicitly exponential, not polynomial.

## The Circular Reasoning

The deepest problem is circular dependency:

```
To construct C(f):
  Need to determine which partial requirements to track
  → Need to know which assignments satisfy which clauses
  → Need to understand f's satisfiability structure
  → This IS the SAT problem we're trying to solve!
```

The construction assumes knowledge of what it's trying to compute.

## Computational Model Mismatch

Feldmann's framework requires:
- **Exact real arithmetic**: probabilities are real numbers in [0,1]
- **Continuous optimization**: LP solvers work in real-number space

Standard complexity theory uses:
- **Discrete Boolean computation**: Turing machines with 0/1 symbols
- **Polynomial time**: polynomial number of Turing machine steps

These are different computational models. Polynomial time in real-number computation (Blum-Shub-Smale model) does not imply polynomial time on a Turing machine.

## The Pattern of Error

This error follows a common pattern in failed P vs NP attempts:

1. **Reformulate the problem** in a different domain (here: Boolean → probabilistic → LP)
2. **Solve the reformulated version** efficiently (here: LP feasibility in polynomial time)
3. **Claim success** for the original problem
4. **Ignore the reformulation cost** (here: constructing the LP is the hard step)

Moving exponential complexity into an unexamined "setup phase" does not eliminate it.

## What Feldmann Actually Proved

- ✓ There exists a mathematical correspondence between SAT formulas and LP systems
- ✓ If such an LP system is given as input, feasibility can be checked in polynomial time
- ✗ The LP system can be constructed from a SAT formula in polynomial time
- ✗ P = NP

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`construction_gap`**: The construction step C : Formula → LPSystem has no polynomial-time algorithm
2. **`exponential_verification`**: Verifying the LP is correct requires examining all 2^N assignments
3. **`circular_dependency`**: Determining working unknowns requires solving SAT

## References

- Feldmann, M. (2020). "Solving satisfiability by Bayesian inference." arXiv:1205.6658v5
- Cook, S. (1971). "The complexity of theorem proving procedures."
- Khachiyan, L. (1979). "A polynomial algorithm in linear programming."
- Blum, L., Shub, M., Smale, S. (1989). "On a theory of computation and complexity over the real numbers."
- Woeginger's List: Entry #90 — https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
