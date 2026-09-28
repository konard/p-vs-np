# Error Analysis: Sauerbier's P=NP Attempt

## Summary

Charles Sauerbier's 2002 claim of polynomial-time algorithms for 3SAT was refuted in September 2003 when a critical error was discovered. This document provides a detailed analysis of the error.

## The Core Claim

Sauerbier claimed three polynomial-time algorithms that could:
1. Determine the existence of satisfying assignments for 3SAT
2. Produce certificates of satisfiability or non-satisfiability
3. Find an instance of a satisfying assignment if one exists

If correct, this would prove P = NP since SAT is NP-complete.

## The Error: "Path Inconsistency"

### Official Description (from Woeginger's list)
> "In September 2003, a hole has been found in the algorithm: An eleventh hour change admits a path inconsistency."

More specifically:
> "An improper closure of a path to a cycle against a root not supportive of the path."

### Technical Explanation

The error occurs in the original algorithm's (version [5]) approach to constraint propagation:

**Problem**: The algorithm restricted its operations to only those elements of structure D (or A) that corresponded to variables appearing in clauses of the CNF expression.

**Why this fails**: This restriction creates what Sauerbier calls "false support" - a situation where:
1. The restricted set of elements appears consistent when checked in isolation
2. But the full problem is actually unsatisfiable
3. The inconsistency only becomes apparent when ALL 3-variable subsets are considered

### Concrete Example (Appendix A of the paper)

Consider a 3SAT instance with:
- Variables: V = {v0, v1, v2, v3, v4}
- 24 carefully constructed clauses (see paper Appendix A)

The clauses are designed such that:
- They admit exactly 8 partial assignments to variable triples
- These 8 assignments form a "chain of resolution"
- This chain creates a cycle that appears satisfiable locally
- But globally, the constraints are inconsistent

The admitted assignments that fool the restricted algorithm:
```
{(-v0, v1, v4), (v0, -v1, v4), (v0, v2, -v3), (-v0, -v2, -v3),
 (-v1, -v2, -v3), (v1, v2, -v3), (-v2, -v3, -v4), (v2, v3, -v4)}
```

When the algorithm only checks the 4 variable triples that have clauses:
- (v0, v1, v4)
- (v0, v2, v3)
- (v1, v2, v3)
- (v2, v3, v4)

It fails to detect the inconsistency that becomes apparent in element (v0, v1, v2), which has no direct clauses but inherits contradictory constraints from the others.

## The "Correction" and Why It Still Fails

### The 2019 Revision

Sauerbier's 2019 revision acknowledges the error and presents "corrected" algorithms that:
1. Operate on ALL 3-variable subsets (not just those with clauses)
2. Propagate constraints across the complete structure
3. Correctly identify the unsatisfiability of the example

### Why This Doesn't Save the P=NP Claim

Even with the correction, several fatal issues remain:

#### 1. **Exponential Structure Size for General SAT**

For a SAT instance with n variables:
- Number of 3-variable subsets: C(n,3) = O(n³)
- Size of structure D or A: O(n³) elements
- Each element stores up to 8 bits (for 3SAT)

**But**: For general k-SAT with k > 3:
- Each element would need 2^k bits
- This grows exponentially

#### 2. **The "A Priori Knowledge" Admission**

Section 5.2 of the paper explicitly states:
> "It is important to note that absent A containing an a priori known set of Boolean sequences (binary strings) and consistent constraints on the variables the algorithm described here is not assured to reliably produce a correct result."

This undermines the entire polynomial-time claim. The algorithm requires:
- Starting with the full set of all possible assignments
- Knowing this set is consistent a priori
- Then reducing it via constraint propagation

This is circular reasoning for proving P=NP.

#### 3. **Hidden Complexity in "Reduce" Operator**

The "reduce" operator (Section 5.3) has claimed worst-case complexity O(|V|⁹), leading to overall complexity O(|V|¹²) for Algorithm 1.

**Problems**:
- This analysis assumes constraint propagation converges quickly
- In pathological cases, the number of iterations could be much higher
- The proof of termination with correct answer is not rigorous

#### 4. **Only Applies to 3SAT, Not General SAT**

The algorithms are specifically designed for 3SAT:
- Use 3-variable subsets
- Use 8-bit bytes for assignment representation
- Complexity analysis depends on the constant "3"

Extending to general SAT would require:
- k-variable subsets (exponential in k)
- 2^k bits per element (exponential)
- This destroys the polynomial-time claim

## The Path Inconsistency Explained

The "path inconsistency" can be understood as follows:

1. **Path**: A sequence of variable assignments that satisfies a subset of clauses
2. **Closure to a cycle**: When these assignments form a circular dependency
3. **Root not supportive**: A variable subset (like (v0, v1, v2) in the example) that doesn't directly have clauses
4. **Inconsistency**: This root element inherits contradictory constraints from the cycle

The original algorithm missed this because it never examined the "root" elements that lack direct clauses.

## Formalization Strategy

To formalize this error, we aim to:

1. **Define the structures** (D and A) as in the paper
2. **Implement the restricted algorithm** (only operates on clause-relevant subsets)
3. **Implement the corrected algorithm** (operates on all subsets)
4. **Construct the counterexample** from Appendix A
5. **Prove**:
   - The restricted algorithm returns SATISFIABLE (incorrectly)
   - The corrected algorithm returns UNSATISFIABLE (correctly)
   - The instance is actually unsatisfiable
6. **Show** the corrected algorithm still doesn't prove P=NP due to complexity and other issues

## Conclusion

Sauerbier's attempt fails because:

1. **The original algorithm is incorrect** - it misses contradictions that only appear in non-clause-bearing variable subsets (the "path inconsistency")

2. **The correction undermines the polynomial claim** - by requiring examination of all O(n³) variable subsets with careful propagation

3. **The approach doesn't extend to general SAT** - it's specific to 3SAT and becomes exponential for larger k

4. **The correctness argument is circular** - it requires knowing the solution set a priori

This is an excellent example of a subtle algorithmic error that appeared plausible on initial inspection but failed under careful scrutiny. The formalization effort helps make the error explicit and verifiable.

## References

1. Sauerbier, C. (2002). "Three complete deterministic polynomial algorithms for 3SAT." arXiv:cs/0205064v3
2. Woeginger, G. "P-versus-NP page" - Entry #6
3. Original paper [5] referenced in the 2002 paper (earlier version with the uncorrected error)
