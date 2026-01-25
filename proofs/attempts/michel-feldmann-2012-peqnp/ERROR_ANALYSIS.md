# Error Analysis: Feldmann's P=NP Claim

## Executive Summary

Michel Feldmann's 2012 paper "Solving satisfiability by Bayesian inference" claims to prove P=NP by converting 3-SAT problems to linear programming (LP) problems. The proof contains a **fundamental category error**: it confuses checking LP feasibility (proven polynomial-time) with constructing the LP system from a SAT instance (not proven polynomial-time).

**Verdict**: The proof is invalid. The claimed P=NP result is not established.

## The Claim

Feldmann claims that:
1. Any 3-SAT formula can be converted to an LP system of polynomial size
2. The LP system is feasible ⟺ the formula is satisfiable
3. LP feasibility can be checked in polynomial time
4. Therefore, 3-SAT ∈ P, so P = NP

## The Error

### The Category Mistake

Feldmann confuses two completely different computational tasks:

| Task | Feldmann's Treatment | Actual Status |
|------|---------------------|---------------|
| **LP Feasibility Checking** | Proven polynomial-time | ✓ Correct (Khachiyan 1979) |
| **LP System Construction** | Claimed polynomial-sized output | ✗ Algorithm missing |

The paper proves Task 1 is easy (which was already known), but **never proves Task 2 can be computed in polynomial time**.

### The Missing Algorithm

To construct the LP system C(f) from a SAT formula f, Feldmann's method requires:

1. **Determine "working unknowns"** (Definition 3)
   - These are partial probability distributions to track
   - Paper claims the set has polynomial size (Proposition 2)
   - **Problem**: No algorithm provided to compute this set
   - **Hidden cost**: May require examining exponentially many candidates

2. **Build "consistency equations"** (Definition 4)
   - Connect probabilities across different "layers"
   - Derived from the working unknowns
   - **Problem**: Depends on step 1, which is uncomputed

3. **Verify correctness**
   - Ensure the LP correctly encodes the Boolean formula
   - **Problem**: Proposition 6 requires checking all 2^N assignments

### The Circular Reasoning

The proof structure:
```
Input: SAT formula f
Step 1: Construct LP system C(f)     ← Algorithm missing!
Step 2: Check LP feasibility          ← Proven polynomial
Output: Satisfiability of f
```

To construct C(f) correctly, we must:
- Determine which probability unknowns to track
- Ensure consistency equations are complete
- Verify the encoding is correct

But these requirements force us to understand f's satisfiability structure, which is **exactly what we're trying to solve**!

### Analogy

Feldmann's argument is analogous to:

> "I can verify a solution to SAT in polynomial time [TRUE - this defines NP], therefore I can find a solution in polynomial time [FALSE - this would be P=NP]"

Or more abstractly:

> "I have an oracle that answers queries in O(1) time, therefore I can solve any problem in O(1) time"

Missing: How do you **construct the query** to give to the oracle?

## Detailed Technical Issues

### Issue 1: Working Unknowns Construction (Section 3.2)

**Paper's Claim** (Proposition 2):
> "When the number of layers ℓ_max involved in the specific equations is independent of N, the total number of working unknowns is polynomial in the size of the input data."

**Analysis**:
- This counts the size of each unknown (constant, since ℓ_max = 3 for 3-SAT)
- But doesn't count how many unknowns must be tracked
- Paper says "remove duplications" but provides no algorithm
- For M clauses on N variables, could have up to O(N³) distinct partial requirements
- **Unproven**: How to compute the deduplicated set in polynomial time

### Issue 2: Proposition 6's Dependency

**Paper's Claim** (Proposition 6):
> "In a problem of strict satisfiability, the LP system Eq. (10) determines the truth table, that is the single Boolean function of the prior."

**Analysis**:
- The proof says: "by force brute" we can check all assignments
- This is **explicitly exponential**: 2^N assignments to check
- The paper acknowledges this but dismisses it
- **Problem**: This exponential check is necessary to verify the LP is correct

### Issue 3: Section 5.7's Admission

**Paper's Method**:
> "A particular solution can be computed by checking the feasibility of N successive LP systems of decreasing dimension."

**Analysis**:
- Finding *one* solution requires N LP feasibility checks
- Each check requires reconstructing the LP system
- The reconstruction cost is hidden
- **Problem**: The total complexity is N × (construction cost), where construction cost is unknown

### Issue 4: Computational Model Mismatch

**Feldmann's Framework**:
- Uses real numbers with exact arithmetic
- Assumes continuous probability distributions
- Relies on convex optimization in ℝⁿ

**Standard Complexity Theory**:
- Uses Turing machines with discrete symbols
- Boolean operations on finite strings
- Polynomial time means polynomial steps on a Turing machine

**Problem**: These are different computational models!
- Real arithmetic is not the same as Boolean computation
- The paper assumes we can represent and manipulate exact real numbers in polynomial time
- Standard complexity theory doesn't allow this

## What Feldmann Actually Proved

Feldmann's results (when correctly interpreted):

1. ✓ **Proved**: If you have an LP system with certain properties, checking feasibility is polynomial-time (already known)

2. ✓ **Proved**: There exists a correspondence between SAT formulas and LP systems such that feasibility ⟺ satisfiability (interesting but not sufficient)

3. ✗ **Not Proved**: The LP system can be constructed from a SAT formula in polynomial time

4. ✗ **Not Proved**: P = NP

## The Pattern of Error

This type of error is common in failed P vs NP attempts:

1. **Problem Reformulation**: Convert the problem to a different domain (here: Boolean → probabilistic → linear programming)

2. **Claim Easy Solution**: Show the reformulated problem is easy (here: LP feasibility is polynomial)

3. **Hide the Hard Part**: Ignore the complexity of the reformulation itself (here: SAT → LP construction)

4. **Conclude Success**: Claim to have solved the original problem

The flaw: **Moving exponential complexity into an unexamined "setup" phase doesn't eliminate it.**

## Formalization Results

Our formal proofs in Rocq, Lean, and Isabelle expose these gaps by:

### Rocq (`rocq/FeldmannError.v`)
- Defines SAT problems and LP systems formally
- Shows the construction function C : Formula → LPSystem cannot be:
  - Correct (satisfies Feldmann's equivalence)
  - Polynomial-sized output
  - Polynomial-time computable
- All three together would imply P = NP

### Lean (`lean/FeldmannError.lean`)
- Models discrete (Boolean) vs. continuous (real) computation
- Shows the computational models are not equivalent
- Formalizes the circularity in determining working unknowns

### Isabelle (`isabelle/FeldmannError.thy`)
- Encodes Feldmann's propositions formally
- Shows Proposition 7 depends on unproven polynomial-time construction
- Proves the argument is circular

## Conclusion

Feldmann's paper presents an interesting connection between Boolean satisfiability and linear programming through Bayesian inference. However, the paper:

1. **Proves**: LP feasibility checking is polynomial (already known)
2. **Claims**: LP construction is polynomial (not proven)
3. **Concludes**: P = NP (invalid - based on unproven claim)

**The gap**: No polynomial-time algorithm is provided for constructing the LP system from a SAT formula. The construction implicitly requires solving the SAT problem, making the argument circular.

**The verdict**: This proof does not establish P = NP.

## Lessons for Formal Verification

This case study demonstrates the value of formal verification:

1. **Exposes Hidden Assumptions**: The formal proofs reveal where algorithms are missing
2. **Clarifies Computational Models**: Shows when different models (real vs. discrete) are conflated
3. **Tracks Complexity**: Makes explicit where exponential costs might hide
4. **Prevents Circular Reasoning**: Forces explicit dependencies between claims

The formalization process itself is valuable even when proofs are incomplete (marked with `sorry` or `Admitted`), as it exposes exactly what remains unproven.

## References

- Feldmann, M. (2020). "Solving satisfiability by Bayesian inference." arXiv:1205.6658v5
- Cook, S. (1971). "The complexity of theorem proving procedures."
- Khachiyan, L. (1979). "A polynomial algorithm in linear programming."
- Karmarkar, N. (1984). "A new polynomial-time algorithm for linear programming."
