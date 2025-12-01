# Michael LaPlante (2015) - P=NP Clique Algorithm Attempt

**Attempt ID**: 102
**Author**: Michael LaPlante
**Year**: 2015
**Claim**: P=NP
**Status**: **REFUTED**

## Summary

In March 2015, Michael LaPlante claimed to establish P=NP by presenting a polynomial-time algorithm for solving the maximum clique problem. The paper "A Polynomial Time Algorithm For Solving Clique Problems" was published on arXiv (arXiv:1503.04794).

In April 2015, Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, and Nathaniel S. Potrepka published a refutation titled "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" (arXiv:1504.06890), demonstrating that LaPlante's algorithm is flawed.

## The Approach

LaPlante's algorithm operates in two phases:

### Phase 1: Neighbor Introductions (Finding 3-Cliques)

The algorithm first finds all 3-cliques in the graph through a "neighbor introduction" process:

1. Each vertex "advertises" its neighbors to all its other neighbors
2. When a vertex learns that one of its neighbors also connects to another of its neighbors, it identifies a 3-clique
3. Each vertex builds a list of all 3-cliques it participates in
4. This phase runs in O(n³) time

### Phase 2: Clique Merging

The algorithm then attempts to merge 3-cliques into larger cliques:

1. For each vertex, examine its "neighborhood" (the set of 3-cliques containing it)
2. Arbitrarily choose a vertex pair from the neighborhood
3. Select one vertex in the pair as the "key node"
4. Search for other pairs containing the key node
5. Check if merging is possible (all necessary vertex pairs exist)
6. Merge compatible pairs to build larger cliques
7. Continue until no more merges are possible
8. Repeat with the next unmerged pair

LaPlante claimed this process correctly identifies all maximal cliques in polynomial time.

## The Error

The refutation paper identifies a **critical flaw in the merging strategy**: the algorithm's arbitrary choices during the merge phase can cause it to miss the maximum clique entirely.

### The Core Problem

LaPlante's algorithm:
- Makes arbitrary choices when selecting which vertex pair to merge next
- **Never backtracks** from these choices
- Assumes that any sequence of valid merges will eventually find the maximum clique

This assumption is **incorrect**. The algorithm can be misled into merging into smaller cliques, preventing it from discovering the actual maximum clique.

### Concrete Counterexample

The refutation paper presents a 15-vertex graph with 5-way rotational symmetry:

```
- Contains one 5-clique with vertices {1, 2, 3, 4, 5}
- Contains ten 4-cliques, each consisting of 3 vertices from the 5-clique plus one additional vertex
- Each combination of 3 vertices from {1, 2, 3, 4, 5} forms a 4-clique with an additional "letter" vertex
```

**What happens:**

When the algorithm processes vertex 1:
1. It finds many 3-cliques in its neighborhood
2. It arbitrarily selects a pair to start merging (e.g., {2, 3})
3. It then looks for another pair containing the key node (say, 2)
4. **Critical choice**: It could merge with {2, 4} (leading to the 5-clique) OR {2, A} (leading to a 4-clique)
5. If it chooses {2, A}, it merges into the 4-clique {1, 2, 3, A}
6. No further merges are possible with this 4-clique
7. The algorithm marks these pairs as "merged" and moves on
8. **The 5-clique is never discovered**

Since the algorithm tries each pair as a starting point but never backtracks within a merge sequence, it's possible that every starting pair leads to a 4-clique instead of the 5-clique.

### Why This Fails the Polynomial Time Claim

The key issues are:

1. **Greedy without backtracking**: The algorithm makes irrevocable choices during merging
2. **No global optimization**: It doesn't consider which merge path leads to the largest clique
3. **Arbitrary selection is insufficient**: LaPlante assumes arbitrary choices don't matter, but they do

To fix the algorithm, one would need to:
- Backtrack through all possible merge sequences
- Try all possible orderings of vertex pairs
- **This requires exponential time**, destroying the polynomial-time claim

## Formal Verification Goal

The goal of this formalization is to:

1. Model the clique problem and LaPlante's algorithm in Coq, Lean, and Isabelle
2. Formalize the counterexample graph from the refutation paper
3. Prove that LaPlante's algorithm **fails** to find the maximum clique on this graph
4. Demonstrate that the algorithm's correctness depends on arbitrary choices
5. Show that guaranteeing correctness would require exponential-time backtracking

## Key Insights

### What LaPlante Got Right
- Finding all 3-cliques efficiently (Phase 1) is correct
- The intuition that cliques can be built from 3-cliques is sound
- Many graphs are correctly solved by the algorithm

### What LaPlante Got Wrong
- **Assumption of path independence**: He assumes the order of merging doesn't affect the final result
- **No proof of convergence to maximum**: He provides no proof that his greedy approach finds the maximum clique
- **Ignoring adversarial graphs**: The counterexample shows carefully constructed graphs can mislead the algorithm

### The Fundamental Lesson

This attempt illustrates a common error in P vs NP attempts:

> **A heuristic that works on many examples is not the same as a correct algorithm that works on all inputs.**

The clique problem is NP-complete precisely because such greedy approaches can be misled. Any polynomial-time algorithm must either:
1. Provide a proof that its strategy cannot be misled, OR
2. Use a fundamentally different approach that avoids the need for backtracking

LaPlante's algorithm does neither.

## References

### Original Paper
- **Title**: A Polynomial Time Algorithm For Solving Clique Problems (And Subsequently, P=NP)
- **Author**: Michael LaPlante
- **Date**: March 9, 2015
- **arXiv**: [1503.04794](https://arxiv.org/abs/1503.04794)
- **Local Copy**: `laplante-original.pdf`

### Refutation Paper
- **Title**: A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami
- **Authors**: Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, Nathaniel S. Potrepka
- **Institution**: Department of Computer Science, University of Rochester
- **Date**: April 26, 2015
- **arXiv**: [1504.06890](https://arxiv.org/abs/1504.06890)
- **Local Copy**: `refutation.pdf`

### From Woeginger's List
- Entry #102: [Woeginger's P-versus-NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## Files in This Directory

- `README.md` - This file
- `laplante-original.pdf` - LaPlante's original paper
- `refutation.pdf` - The refutation by Cardenas et al.
- `coq/` - Coq formalization of the counterexample
- `lean/` - Lean formalization of the counterexample
- `isabelle/` - Isabelle/HOL formalization of the counterexample

## Related Work

This is part of issue #44: **Test all P vs NP attempts formally**

The goal is to formalize incorrect P vs NP proofs to:
1. Understand common error patterns
2. Build a library of counterexamples
3. Develop automated tools for detecting similar errors
4. Educate researchers about pitfalls in complexity theory proofs
