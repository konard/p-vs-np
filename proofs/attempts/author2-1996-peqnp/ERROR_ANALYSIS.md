# Error Analysis: Plotnikov's 1996 P=NP Attempt

## Summary

Plotnikov's 1996 paper claims to solve the clique partition problem in polynomial time (O(n⁵)), which would prove P=NP. Our formalization across three proof assistants (Coq, Lean, and Isabelle) reveals where this proof attempt likely fails.

## The Central Claim

**Claim**: There exists a polynomial-time algorithm that finds the **minimum** clique partition of any graph.

**Consequence**: If true, this would prove P=NP, as the clique partition problem is NP-complete.

## The Most Likely Error: Optimality vs. Correctness

### What's Easy: Finding A Partition

Finding **any** clique partition is trivial in polynomial time:
- Solution: Make each vertex its own clique
- Time complexity: O(n)
- Result: A valid partition of size n

### What's Hard: Finding THE MINIMUM Partition

Finding the **minimum** clique partition is NP-complete:
- No polynomial-time algorithm is known
- Remains hard even with restrictions (cubic planar graphs, etc.)
- Equivalent to graph coloring on the complement graph

### The Critical Distinction

The error almost certainly lies in **confusing these two problems**:

1. **Correctness Proof** (probably sound):
   - "The algorithm produces a valid clique partition"
   - This may be provable and correct

2. **Optimality Proof** (likely has a gap):
   - "The algorithm produces a MINIMUM clique partition"
   - This is where the proof almost certainly breaks down

## Identified Gaps in the Formalization

### Gap 1: The Optimality Axiom

In all three formalizations, we had to axiomatize:

```
axiom plotnikov_optimality:
  The partition produced is MINIMUM (not just valid)
```

This axiom is almost certainly **unprovable** because:
- It would imply P=NP
- No such algorithm is known to exist
- The claim contradicts fundamental complexity theory

### Gap 2: Information Loss in Graph-to-Poset Mapping

The approach uses partial orders, but:

1. **What might be proven**: The poset captures some graph structure
2. **What cannot be proven**: The poset preserves enough information to recover the minimum partition
3. **The gap**: The mapping likely loses critical structural information needed for optimality

### Gap 3: Hidden Assumptions

Common errors in such proofs:

1. **Assuming properties that don't hold universally**
   - May work on special graph classes (perfect graphs)
   - Fails on general graphs

2. **Local vs. Global Optimality**
   - May find locally optimal partitions
   - But not globally minimum ones

3. **Incomplete case analysis**
   - May not consider all possible graph structures
   - Edge cases where the algorithm fails

## Why This Problem is Actually Hard

### Theoretical Evidence

1. **NP-Completeness** (Karp, 1972)
   - Reduction from graph 3-coloring
   - Reduction from other NP-complete problems

2. **Equivalence to Graph Coloring**
   - G can be partitioned into k cliques ↔ complement of G is k-colorable
   - Graph coloring is NP-complete

3. **No Polynomial-Time Algorithm Known**
   - Despite extensive research for 50+ years
   - Would be a Clay Millennium Prize-winning result

### Practical Evidence

1. **Hardness on Restricted Classes**
   - Remains NP-complete on cubic planar graphs
   - Remains NP-complete on unit disk graphs

2. **Inapproximability Results**
   - Hard to approximate within certain factors
   - No PTAS unless P=NP

3. **Barrier Results**
   - Relativization barrier
   - Natural proofs barrier
   - Algebrization barrier

## What Plotnikov's Algorithm Likely Does

### Most Probable Reality

1. **Produces a valid partition**: ✓ (Probably correct)
2. **Runs in polynomial time**: ✓ (Possibly O(n⁵) as claimed)
3. **Finds the minimum partition**: ✗ (Almost certainly incorrect)

### What It Might Actually Be

The algorithm is likely:
- A **heuristic** that finds good (but not optimal) partitions
- An **approximation algorithm** with some approximation factor
- A **correct algorithm for special graph classes** (perfect graphs)
- A **misinterpreted algorithm** that solves a different problem

## Lessons from Formalization

### 1. Precision Matters

Informal proofs can hide the difference between:
- "finds a partition" vs. "finds the minimum partition"
- "works on examples" vs. "works on all inputs"
- "usually optimal" vs. "always optimal"

### 2. Axioms Reveal Gaps

Having to axiomatize the optimality claim reveals:
- This is the unprovable part
- This is where the proof must fail
- This is what needs extraordinary evidence

### 3. Type Systems Catch Errors

The formalization forced us to distinguish:
- `Partition` (any partition)
- `MinimumPartition` (optimal partition)
- The algorithm returns the former, but claims the latter

## Conclusion

**The Error**: The proof almost certainly has a gap in the optimality argument. The algorithm may produce **a** clique partition in polynomial time, but not **the minimum** clique partition.

**Why It Matters**: This is a common mistake in attempted P=NP proofs:
- Solving the easy version of the problem
- Claiming to have solved the hard version
- Not rigorously proving optimality for all cases

**Verification Value**: Formal verification exposes these gaps by requiring:
- Precise definitions
- Complete proofs
- No hand-waving about "obviously optimal" claims

Without access to the full paper, we cannot identify the exact line where the proof breaks. However, the gap is almost certainly in proving that the algorithm finds the **minimum** partition, not just any partition.

## References

1. **Karp, R. M.** (1972). "Reducibility among combinatorial problems"
2. **Garey, M. R., & Johnson, D. S.** (1979). "Computers and Intractability"
3. **Woeginger, G. J.** P-versus-NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

---

*This analysis is based on formalizing the claimed algorithm in Coq, Lean, and Isabelle without access to the full paper. The error identification is based on complexity theory principles and common patterns in failed P=NP attempts.*
