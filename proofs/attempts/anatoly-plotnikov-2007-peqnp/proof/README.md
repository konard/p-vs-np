# Forward Proof Formalization: Plotnikov 2007

This directory contains a partial sketch of Plotnikov's approach. Its abstract graph definitions and axioms do not verify the algorithm or Conjecture 1. See the [refutation audit](../refutation/README.md) for a sound conditional formulation.

## Contents

- `lean/PlotnikovProof.lean` - Lean 4 formalization
- `rocq/PlotnikovProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **Vertex-Saturated Digraph Construction**: Transform undirected graph into VS-digraph using "cutting" operations
2. **Transitive Closure Graph**: Build poset representation via TCG
3. **Minimum Chain Partition**: Apply Ford-Fulkerson methodology for poset partitioning
4. **Conjecture 1 (UNPROVEN)**: The critical assumption upon which algorithm correctness depends
5. **Polynomial Time Claim**: O(n⁸) complexity assertion

## The Attempted Proof Logic

Plotnikov's argument proceeds:

1. **Initialize with MIS**: Find an initial maximal independent set V⁰
2. **Build Acyclic Digraph**: Partition vertices into layers and orient edges
3. **Construct VS-Digraph**: Apply Algorithm VS using "cutting" operations σ_W
4. **Search for MMIS**: Use Conjecture 1 to find fictitious arcs whose removal increases independent set size
5. **Iterate**: Repeat until no improvement possible
6. **Conclusion**: Since MISP is NP-complete and solvable in O(n⁸), P = NP

## Where the Formalizations Stop

The forward files introduce unproved claims with `axiom` (Lean) and `Axiom` (Rocq). These are placeholders, not established results:

1. **Conjecture 1**: The paper explicitly states (Theorem 5, page 9):
   > "**If the conjecture 1 is true** then the stated algorithm finds a MMIS of the graph G ∈ Lₙ."

   This conjecture is STATED but NEVER PROVEN. The author provides no proof, only empirical testing on random graphs.

2. **VS-Digraph Construction Correctness**: The properties of vertex-saturated digraphs and their relationship to MMIS optimality are assumed

3. **Complexity Bounds**: The O(n⁸) analysis assumes the number of iterations is bounded by O(n), which depends on Conjecture 1

## The Core Error

From the paper (page 9, Theorem 5):

> "**If the conjecture 1 is true** then the stated algorithm finds a MMIS of the graph G ∈ Lₙ."

**This conditional statement means:**
- The stated conditional argument needs Conjecture 1 to establish correctness
- Conjecture 1 is nowhere proven in the paper
- Therefore, algorithm correctness is NOT established
- Therefore, the claim that P = NP is INVALID

**The author's defense (page 9):**
> "The pascal-programs were written for the proposed algorithm. Long testing the program for random graphs has shown that the algorithm runs stably and correctly."

**Why this is insufficient:**
- Empirical testing on random graphs ≠ mathematical proof
- A counterexample may exist that was not encountered in testing
- Mathematical claims require rigorous proof, not experimental validation

## Additional Issues

### Issue 1: Non-Constructive Use of Dilworth's Theorem

Plotnikov relies on minimum chain partitions (MCP) of partially ordered sets. For finite posets these can be computed through polynomial-time bipartite matching; the missing part is a proof that the paper's graph construction and later operations have the required properties:

- The Ford-Fulkerson method supplies a matching subroutine
- The correspondence between poset antichains and graph independent sets requires careful proof
- The complexity of the full graph algorithm needs its own analysis

### Issue 2: Complexity Analysis Gaps

The O(n⁸) analysis (Theorem 6) makes unverified assumptions:
- Assumes exactly O(n) iterations needed
- Assumes each iteration increases independent set size by 1
- Depends on Conjecture 1 being true for the iteration bound

### Issue 3: Lack of Rigorous Proofs

Throughout the paper:
- Many theorems marked "Q.E.D." without detailed proofs
- "It is obviously" used without justification
- The "cutting" operation's properties are assumed, not proven

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
