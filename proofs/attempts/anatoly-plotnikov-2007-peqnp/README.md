# Anatoly D. Plotnikov (2007) - P=NP Attempt

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

**Attempt ID**: 39 (from Woeginger's list)
**Author**: Anatoly D. Plotnikov
**Year**: 2007
**Claim**: P = NP
**Paper Title**: "Experimental Algorithm for the Maximum Independent Set Problem"
**Publication**: arXiv:0706.3565 (2007); later published in Cybernetics and Systems Analysis, Vol. 48, Issue 5 (2012), pp. 673-680
**Status**: Refuted (relies on unproven conjecture)

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

The fundamental error in Plotnikov's proof is that **the entire algorithm's correctness depends on an unproven Conjecture 1**, which the author admits has not been proven.

### Critical Flaw: Reliance on Unproven Conjecture

**Location**: Section 4, page 9 of the paper

**Conjecture 1** (stated by Plotnikov):
> "Let a saturated digraph G⃗(V⁰) has an independent set U ⊂ V such that Card(U) > Card(V⁰). Then it will be found a fictitious arc vᵢ ≫ vⱼ such that in the digraph G⃗(Z⁰), induced by removing this arc, the relation Card(Z⁰) ≥ Card(V⁰) - 1 is satisfied."

**Why this is fatal**:

1. **Algorithm correctness depends on the conjecture** (Theorem 5, page 9):
   > "**If the conjecture 1 is true** then the stated algorithm finds a MMIS of the graph G ∈ Lₙ."

2. **No proof is provided**: The paper offers no proof of Conjecture 1. The author merely states it and builds the algorithm upon it.

3. **Circular reasoning**: The conjecture essentially assumes that the algorithm's greedy approach will work, without proving it.

4. **Empirical testing is insufficient**: The author claims:
   > "The pascal-programs were written for the proposed algorithm. Long testing the program for random graphs has shown that the algorithm runs stably and correctly."

   However, testing on random graphs does not constitute a proof. A counterexample could exist that was not encountered in testing.

### Additional Issues

#### Issue 1: Non-Constructive Use of Dilworth's Theorem

**Location**: Throughout the algorithm, particularly in the VS construction

Plotnikov relies on finding minimum chain partitions (MCP) of partially ordered sets. While Dilworth's Theorem guarantees existence, **computing the MCP is itself computationally hard** for general posets:

- The Ford-Fulkerson algorithm mentioned works for bipartite matching in O(n^5/2)
- However, the correctness of applying this to the specific posets constructed from graphs is not rigorously established
- The correspondence between poset antichains and graph independent sets is assumed but not fully proven

#### Issue 2: Complexity Analysis Gaps

**Location**: Theorem 6, page 9

The O(n⁸) complexity analysis makes several assumptions:

- Assumes exactly O(n) iterations are needed in the worst case
- Assumes each iteration increases the independent set size by 1
- Does not account for potential exponential blowup in special cases
- The claimed polynomial bound depends on Conjecture 1 being true

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

## Formalization Strategy

To verify and understand the errors, we formalize the proof in three theorem provers:

### 1. Coq (`coq/` directory)
- Define graphs, independent sets, and digraphs formally
- Formalize the vertex-saturated digraph construction
- Attempt to prove Conjecture 1 or construct a counterexample
- Show the algorithm's correctness gap

### 2. Lean 4 (`lean/` directory)
- Use Mathlib's graph theory library
- Define the MISP problem formally
- Implement Plotnikov's algorithm structure
- Prove that without Conjecture 1, correctness cannot be established

### 3. Isabelle/HOL (`isabelle/` directory)
- Use Isabelle's graph theory and complexity frameworks
- Formalize the algorithm step-by-step
- Use automated provers to identify gaps in reasoning
- Attempt to find counterexamples to Conjecture 1

## Formalization Goals

Each formalization aims to:

1. **Define the problem**: Formal specification of MISP
2. **Model the algorithm**: Implement Plotnikov's approach
3. **Identify the gap**: Show where Conjecture 1 is needed
4. **Assess completeness**: Determine if Conjecture 1 could be proven or if counterexamples exist
5. **Verify complexity**: Check if the claimed O(n⁸) bound is sound given the assumptions

## Known Refutation

While there is no published explicit refutation of Plotnikov's specific paper, the claim contradicts:

- **Widespread belief that P ≠ NP**: Based on decades of failed attempts
- **Lack of verification**: If correct, this would have won the Clay Millennium Prize ($1 million)
- **Community consensus**: No acceptance by the theoretical computer science community
- **Unproven conjecture**: The author himself acknowledges the algorithm's correctness depends on an unproven conjecture

The paper appeared on arXiv but was never validated or accepted by mainstream complexity theory conferences or journals as a valid proof.

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
├── coq/
│   └── PlotnikovMISP.v
├── lean/
│   └── PlotnikovMISP.lean
└── isabelle/
    ├── PlotnikovMISP.thy
    └── ROOT
```

## Status

- [ ] Coq formalization
- [ ] Lean formalization
- [ ] Isabelle formalization
- [ ] Formal identification of conjecture dependency
- [ ] Counterexample search for Conjecture 1
- [ ] Complexity analysis verification

## Key Lessons

1. **Unproven conjectures invalidate proofs**: A proof that depends on an unproven conjecture is not a proof of the original claim
2. **Empirical testing ≠ Mathematical proof**: Testing on random graphs cannot replace rigorous mathematical proof
3. **NP-completeness is robust**: Decades of failed attempts suggest P ≠ NP remains the likely answer
4. **Algorithmic claims need rigorous analysis**: Polynomial-time claims for NP-complete problems require extraordinary evidence
5. **Poset techniques have limitations**: While Ford-Fulkerson's method is powerful, it doesn't automatically solve NP-hard problems
6. **Circular reasoning trap**: Assuming the algorithm works to prove the algorithm works is a common error in P vs NP attempts

---

*This formalization is part of the [P vs NP formal verification project](../../..) - Issue #444, PR #506*

[← Back to Attempts](../) | [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)
