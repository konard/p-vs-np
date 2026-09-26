# Anatoly D. Plotnikov (2007) - P=NP Attempt

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

**Attempt ID**: 39 (from Woeginger's list)
**Author**: Anatoly D. Plotnikov
**Year**: 2007
**Claim**: P = NP
**Paper Title**: "Experimental Algorithm for the Maximum Independent Set Problem"
**Publication**: arXiv:0706.3565 (2007); later published in Cybernetics and Systems Analysis, Vol. 48, Issue 5 (2012), pp. 673-680
**Status**: P = NP claim unproved (correctness is conditional on Conjecture 1)

## Summary

In June 2007, Ukrainian mathematician Anatoly D. Plotnikov published a paper claiming to provide an O(n⁸) polynomial-time algorithm for the maximum independent set problem (MISP). Since MISP is NP-complete, a polynomial-time exact algorithm would prove P = NP. This was Plotnikov's second attempt at proving P = NP; his first attempt in 1996 (entry #2 on Woeginger's list) tackled the related clique partition problem.

## Main Argument/Approach

### The Maximum Independent Set Problem

The **maximum independent set problem** asks: Given an undirected graph G = (V, E), find the largest subset U ⊆ V of vertices such that no two vertices in U are connected by an edge.

**Key Facts**:
- **Input**: An undirected graph G = (V, E) with n vertices
- **Output**: A maximum independent set (MMIS) - an independent set of maximum cardinality
- The decision version ("Does G have an independent set of size ≥ k?") is NP-complete
- The optimization version is NP-hard
- Equivalent to finding the maximum clique in the complement graph

### Plotnikov's Algorithm Strategy

Plotnikov's approach consists of three main components:

1. **Graph-to-Digraph Transformation**: Convert the undirected graph into an acyclic directed graph (digraph) by partitioning vertices into layers V⁰, V¹, ..., Vᵐ where V⁰ is an initial maximal independent set (MIS).

2. **Poset Representation**: Construct the transitive closure graph (TCG), which represents a partially ordered set (poset). Apply Ford-Fulkerson's methodology for partitioning posets into minimum chains and finding maximum antichains.

3. **Vertex-Saturated Digraph Construction**: Iteratively refine the digraph through "cutting" operations (reorienting arcs) until achieving a "vertex-saturated" (VS) digraph with special properties.

4. **Conjecture-Based Search**: Use **Conjecture 1** to systematically search for fictitious arcs whose removal increases the size of the independent set, eventually finding the MMIS.

### Claimed Complexity

The paper claims O(n⁸) time complexity:
- Constructing a VS-digraph: O(n⁵) (Theorem 3)
- Finding MMIS by testing fictitious arcs: O(n²) arcs × O(n⁵) per test × O(n) iterations = O(n⁸) (Theorem 6)

## The Error in the Proof

The paper's stated correctness argument depends on Conjecture 1, for which it provides no proof. This leaves its P = NP conclusion unestablished; it does not establish that Conjecture 1 or the algorithm is false.

### Critical Flaw: Reliance on Unproven Conjecture

**Location**: Section 4, page 9 of the paper

**Conjecture 1** (stated by Plotnikov):
> "Let a saturated digraph G⃗(V⁰) has an independent set U ⊂ V such that Card(U) > Card(V⁰). Then it will be found a fictitious arc vᵢ ≫ vⱼ such that in the digraph G⃗(Z⁰), induced by removing this arc, the relation Card(Z⁰) ≥ Card(V⁰) - 1 is satisfied."

**Missing steps**:

1. **Algorithm correctness depends on the conjecture** (Theorem 5, page 9):
   > "**If the conjecture 1 is true** then the stated algorithm finds a MMIS of the graph G ∈ Lₙ."

2. **No proof is provided**: The paper offers no proof of Conjecture 1. The author merely states it and builds the algorithm upon it.

3. **Empirical testing is insufficient**: The author claims:
   > "The pascal-programs were written for the proposed algorithm. Long testing the program for random graphs has shown that the algorithm runs stably and correctly."

   However, testing on random graphs does not constitute a proof. A counterexample could exist that was not encountered in testing.

### Additional Issues

#### Issue 1: Graph and Poset Correspondence

**Location**: Throughout the algorithm, particularly in the VS construction

Plotnikov uses minimum chain partitions (MCP) of partially ordered sets. These can be computed via polynomial-time bipartite matching for finite posets. The remaining question is whether the particular graph-to-poset construction and cutting operations have the claimed properties:

- The correctness of applying the matching method to the specific posets constructed from graphs needs justification
- The correspondence between the resulting antichains and graph independent sets needs a proof

#### Issue 2: Complexity Analysis Gaps

**Location**: Theorem 6, page 9

The O(n⁸) complexity analysis makes several assumptions:

- Assumes O(n) successful iterations in the worst case
- Requires a proof that each successful iteration increases the independent set size
- Requires a bound on all attempted arc tests and reconstruction work
- The displayed O(n⁸) estimate is not a formal bound on an implemented running-time function

#### Issue 3: Lack of Rigorous Proofs

Throughout the paper:

- Many theorems are stated as "Q.E.D." or "It is obviously" without detailed proofs
- The correctness of the "cutting" operation σ_W preserving graph properties is not fully established
- The relationship between vertex-saturation and MMIS optimality is assumed

## Why This Problem Is Hard

The maximum independent set problem remains NP-complete because:

- **Karp's 21 NP-complete problems** (1972): MISP is among the original set
- **Reduction from 3-SAT**: Can be reduced from Boolean satisfiability
- **Inapproximability**: Hard to approximate within factor n^(1-ε) for any ε > 0 (unless P=NP)
- **Complement to clique**: Finding maximum independent set in G equals finding maximum clique in complement Ḡ
- **No known polynomial algorithm**: Despite decades of research, no polynomial-time exact algorithm exists
- **Successful algorithms**: Only exponential-time exact algorithms (e.g., O(1.2^n)) and polynomial-time approximations with weak guarantees

## Formalization Scope

The forward Lean and Rocq files sketch Plotnikov's graph definitions and claims. They contain placeholders and unproved axioms, so compilation of those files does not verify the paper's algorithm. The refutation files state Conjecture 1 as a conditional property of VS-digraph instances and model Theorem 5 as an explicit hypothesis. They prove the conditional consequence only when both the hypothesis and Conjecture 1 are supplied. They also prove that a cubic running time is polynomial under the local definition, correcting the old contradictory axiom.

The following proof obligations remain open: a faithful graph-level definition of a qualifying fictitious arc, a proof of Conjecture 1, a proof of Theorem 5 for the implemented algorithm, and a bound on that algorithm's running time. The refutation formalizations prove neither a counterexample to Conjecture 1 nor that Plotnikov's algorithm is incorrect.

## References

1. **Original Paper**: Plotnikov, A. D. (2007). "Experimental Algorithm for the Maximum Independent Set Problem." arXiv:0706.3565 [cs.DS]. https://arxiv.org/abs/0706.3565

2. **Published Version**: Plotnikov, A. D. (2012). "Experimental Algorithm for the Maximum Independent Set Problem." *Cybernetics and Systems Analysis*, Vol. 48, Issue 5, pp. 673-680.

3. **Woeginger's List**: Entry #39 on Gerhard Woeginger's "The P-versus-NP page"
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

4. **Plotnikov's First Attempt**: Entry #2 (1996) - "Polynomial-Time Partition of a Graph into Cliques"
   See `../author2-1996-peqnp/` in this repository

5. **Ford-Fulkerson Algorithm**: Ford, L. R. and Fulkerson, D. R. (1962). *Flows in Networks*. Princeton University Press.

6. **Dilworth's Theorem**: Dilworth, R. P. (1950). "A decomposition theorem for partially ordered sets." *Annals of Mathematics*, 51(1), pp. 161-166.

7. **MISP Complexity**: Garey, M. R. and Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*. W.H. Freeman.

## Directory Structure

```
anatoly-plotnikov-2007-peqnp/
├── README.md (this file)
├── ORIGINAL.md and ORIGINAL.pdf
├── proof/
│   ├── lean/PlotnikovProof.lean
│   └── rocq/PlotnikovProof.v
└── refutation/
    ├── lean/PlotnikovRefutation.lean
    └── rocq/PlotnikovRefutation.v
```

## Status

- [x] Lean and Rocq conditional audit of the conjecture dependency
- [ ] Complete graph-level formalization of the algorithm
- [ ] Proof of Conjecture 1 and the conditional correctness theorem
- [ ] Counterexample search for Conjecture 1
- [ ] Complexity analysis verification

## Key Lessons

1. **Unproven conjectures invalidate proofs**: A proof that depends on an unproven conjecture is not a proof of the original claim
2. **Empirical testing ≠ Mathematical proof**: Testing on random graphs cannot replace rigorous mathematical proof
3. **Correctness and running time are separate obligations**: A conditional correctness statement does not establish the claimed O(n⁸) bound
4. **Graph transformations need proofs**: A polynomial-time matching subroutine alone does not establish correctness of the full algorithm

---

*This formalization is part of the [P vs NP formal verification project](../../..) - Issue #444, PR #506*

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
