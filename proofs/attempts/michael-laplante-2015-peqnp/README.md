# Michael LaPlante (2015) - P=NP via Maximum Clique Algorithm

**Attempt ID**: 102 (from Woeginger's list)
**Author**: Michael LaPlante
**Year**: 2015
**Claim**: P=NP
**Paper**: "A Polynomial Time Algorithm For Solving Clique Problems (And Subsequently, P=NP)"
**arXiv**: [1503.04794](http://arxiv.org/abs/1503.04794)
**Status**: **REFUTED**

## Summary

In March 2015, Michael LaPlante published a paper claiming to prove P=NP by presenting a polynomial-time algorithm for solving the maximum clique problem, which is known to be NP-complete. The algorithm operates in two phases:

1. **Phase 1 (Neighbor Introductions)**: For each vertex in the graph, find all 3-cliques containing it by having vertices "communicate" their neighbors to each other.

2. **Phase 2 (Clique Calculation)**: Merge the discovered 3-cliques into larger cliques by iterating through vertex pairs and checking for merge conditions.

LaPlante claimed this algorithm runs in polynomial time: O((n-1)(n-2)(n-3)) for Phase 1 and O(n((n-1)(n-2))/2) for Phase 2 in a complete graph.

## Refutation

In April 2015, Cardenas, Holtz, Janczak, Meyers, and Potrepka published a refutation: "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" ([arXiv:1504.06890](http://arxiv.org/abs/1504.06890)).

### The Critical Error

The refutation identifies a **fundamental flaw in Phase 2's merging logic**: the algorithm makes arbitrary choices when selecting which vertex pairs to merge, and **does not backtrack** when a wrong choice is made. This causes the algorithm to miss the maximum clique in certain graphs.

### Counterexample

The refutation presents a 15-vertex graph with 5-fold rotational symmetry containing:
- A central 5-clique (vertices 1, 2, 3, 4, 5)
- Ten 4-cliques, each consisting of 3 vertices from the 5-clique plus one additional "outer" vertex (labeled A-J)

**Key insight**: Every combination of 3 vertices from the 5-clique appears in some 4-clique with an outer vertex. This means every vertex pair in the 5-clique can potentially be merged with an outer vertex, creating a 4-clique and missing the 5-clique entirely.

#### Why the Algorithm Fails

When analyzing vertex 1's neighborhood:
- Phase 1 correctly identifies all 3-cliques containing vertex 1
- Phase 2 must arbitrarily choose a starting vertex pair (e.g., {2, 3})
- This pair can merge with either:
  - Another number pair (e.g., {2, 4}) → potentially finds the 5-clique
  - A letter pair (e.g., {2, A}) → finds only a 4-clique and stops

**The problem**: LaPlante's algorithm never specifies a strategy for choosing merges and never backtracks. If the algorithm consistently makes the "wrong" choice (merging with letter vertices), it will discover only 4-cliques and report 4 as the maximum clique size, when the correct answer is 5.

### The Merging Ambiguity

LaPlante states: "The order does not matter" and chooses pairs "arbitrarily." However, the refutation proves that **order does matter** - different orderings lead to different outcomes. Without backtracking, the algorithm cannot guarantee finding the maximum clique.

## The Error in Formal Terms

**What the algorithm claims to do**:
- Find the maximum clique in polynomial time O(n^k) for some constant k

**What the algorithm actually does**:
- Find **a** maximal clique (possibly not maximum) in polynomial time
- Uses a greedy heuristic that can get stuck in local maxima

**Why the claim fails**:
- **Missing specification**: The algorithm doesn't specify which vertex pair to choose when multiple pairs have equal priority
- **No backtracking**: Once a merge path is chosen, the algorithm never reconsiders
- **Exists a graph family**: For the counterexample graph, there exist execution paths where the algorithm provably fails to find the maximum clique
- **Cannot be fixed in polynomial time**: Adding complete backtracking would make the algorithm exponential, not polynomial

## Complexity Theory Insight

This attempt falls into a classic trap in complexity theory:

1. **Easy to verify**: Given a clique, verifying it is a clique takes O(k²) time
2. **Hard to find**: Finding the maximum clique (without backtracking) can lead to wrong answers
3. **Greedy doesn't work**: The clique problem doesn't have the optimal substructure needed for greedy algorithms
4. **NP-completeness**: The maximum clique problem is NP-complete, meaning unless P=NP, no polynomial-time algorithm exists

## Formalization Goals

This formalization aims to:

1. **Define the clique problem** formally in Coq, Lean, and Isabelle
2. **Formalize LaPlante's algorithm** including its two phases
3. **Construct the counterexample graph** from the refutation
4. **Prove the algorithm fails** on the counterexample by showing:
   - The graph contains a 5-clique
   - There exists an execution path of the algorithm that returns 4
   - Therefore, the algorithm is incorrect

## Files

- `coq/LaPlante2015.v` - Coq formalization
- `lean/LaPlante2015.lean` - Lean formalization
- `isabelle/LaPlante2015.thy` - Isabelle formalization

## Key Definitions

### Clique
A set of vertices C in a graph G = (V, E) where every pair of distinct vertices in C is connected by an edge.

### k-Clique Decision Problem
Given a graph G and integer k, determine whether G contains a clique of size at least k.

### Maximum Clique Problem
Given a graph G, find the largest clique in G.

### LaPlante's Algorithm (Simplified)
```
Phase 1: For each vertex v:
  - Find all 3-cliques containing v
  - Store as list of vertex pairs

Phase 2: For each vertex v:
  - Pick unmerged vertex pair p = {a, b}
  - Set key_node = a (arbitrary choice)
  - For each other pair p' containing key_node:
    - Check if merge conditions satisfied
    - If yes, merge p and p'
  - Repeat until no more merges possible
  - Record size of merged clique
```

### The Bug
**Line**: "Pick unmerged vertex pair p" and "Set key_node = a (arbitrary choice)"
**Issue**: "Arbitrary" choice + no backtracking = potential failure
**Fix required**: Backtracking through all choices (exponential time!)

## References

1. LaPlante, M. (2015). "A Polynomial Time Algorithm For Solving Clique Problems." arXiv:1503.04794
2. Cardenas, H. A., Holtz, C., Janczak, M., Meyers, P., & Potrepka, N. S. (2015). "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890
3. Woeginger, G. J. "The P-versus-NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Educational Value

This failed proof attempt demonstrates:

1. **Greedy algorithms don't always work**: The clique problem lacks optimal substructure
2. **Verification ≠ Solution**: Verifying a clique is easy; finding the maximum is hard
3. **Importance of formal proof**: Informal arguments can hide subtle errors
4. **Value of counterexamples**: A single counterexample refutes a universal claim
5. **Backtracking vs polynomial time**: Complete search requires exponential time

## Conclusion

LaPlante's algorithm is a **heuristic** that works on many graphs but fails on a precisely constructed counterexample. The error is subtle: the algorithm appears to work because it finds **a** large clique, just not always the **maximum** clique. This highlights why P vs NP is so difficult - many plausible approaches fail on carefully crafted counterexamples.

The formalization in this directory makes the error explicit and verifiable, contributing to our understanding of why certain approaches to P=NP cannot work.
