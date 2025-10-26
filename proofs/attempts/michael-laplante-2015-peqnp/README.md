# Michael LaPlante (2015) - P=NP Proof Attempt

**Attempt ID**: 102 (from Woeginger's list)
**Author**: Michael LaPlante
**Year**: 2015
**Claim**: P=NP
**Paper**: "A Polynomial Time Algorithm For Solving Clique Problems (And Subsequently, P=NP)"
**arXiv**: [1503.04794](http://arxiv.org/abs/1503.04794)
**Refutation**: Cardenas et al. (2015), [arXiv:1504.06890](http://arxiv.org/abs/1504.06890)

## Summary

Michael LaPlante claimed to establish P=NP by presenting a polynomial-time algorithm for solving the maximum clique problem, which is NP-complete. The approach consists of two phases:

1. **Phase 1 (Neighbor Introductions)**: Each vertex identifies all 3-cliques it belongs to by having vertices "communicate" and share information about their neighbors.

2. **Phase 2 (Clique Calculation)**: Each vertex merges its 3-cliques into larger cliques by iteratively combining vertex pairs that share a "key node."

LaPlante argued that since the clique problem is NP-complete, a polynomial-time solution to it would prove P=NP.

## Main Argument

### The Algorithm

**Phase 1**: For each vertex v in the graph:
- v tells each of its neighbors about all its other neighbors
- When a vertex learns about a neighbor of its neighbor that it is also connected to, it identifies a 3-clique
- Running time claimed: O((n-1)(n-2)(n-3)) for a complete graph with n vertices

**Phase 2**: For each vertex v:
- Build a list of "vertex pairs" from the 3-cliques found in Phase 1
- Arbitrarily choose a vertex pair and designate one vertex as the "key node"
- Iterate through other vertex pairs looking for pairs containing the key node
- Before merging, verify that the new vertex is paired with all vertices in the current merged list
- Continue until no more pairs can be merged
- The result is a maximal clique

**Claim**: Both phases run in polynomial time, therefore the entire algorithm solves the maximum clique problem in polynomial time, proving P=NP.

### Complexity Analysis

LaPlante's analysis:
- **Phase 1**: O(n³) for complete graphs
- **Phase 2**: O(n · p · (p-1)) where p is the number of pairs for a given node
- **Overall claim**: Polynomial time

## The Refutation

In April 2015, Cardenas, Holtz, Janczak, Meyers, and Potrepka published a refutation identifying a critical flaw in LaPlante's algorithm.

### The Core Error

**Problem**: The algorithm makes **arbitrary choices** during Phase 2 when selecting which vertex pairs to merge, and it **never backtracks** from these choices.

**Fatal Flaw**: When multiple vertex pairs have equal priority, the algorithm may choose to merge pairs that lead to discovering only a 4-clique, missing a larger 5-clique that exists in the graph.

### Counterexample

The refutation presents a graph with 15 vertices containing:
- A central 5-clique (vertices 1, 2, 3, 4, 5)
- Ten 4-cliques, each consisting of 3 vertices from the 5-clique plus one additional "outer" vertex (labeled A-J)

**Why the algorithm fails**:

1. When processing vertex 1 (part of the 5-clique), the algorithm sees vertex pairs like {2,3}, {2,4}, {2,A}, {3,A}, etc.

2. If it starts with pair {2,3} (a number-number pair), it could next merge with:
   - {2,4}, {2,5}, {3,4}, or {3,5} → leading to the 5-clique (correct)
   - {2,A} or {3,A} → leading to the 4-clique {1,2,3,A} (incorrect)

3. The algorithm provides **no guidance** on which merge to choose.

4. If the algorithm always chooses to merge with a letter vertex (outer vertices), it will discover only 4-cliques and miss the 5-clique entirely.

5. Since the algorithm **never backtracks**, once it commits to a merge path leading to a 4-clique, it cannot recover and find the 5-clique.

### The General Counterexample

The refutation also provides a family of counterexamples for any k ≥ 4:
- Construct three cliques: Cₖ, Cₖ₋₁, and C'ₖ₋₁
- Connect them in a specific pattern
- Any algorithm following LaPlante's approach can be forced to miss the k-clique

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the graph structure** for cliques and adjacency
2. **Formalizing Phase 1** (neighbor introductions) to show it correctly identifies 3-cliques
3. **Formalizing Phase 2** (clique merging) with its arbitrary choice points
4. **Constructing the counterexample** graph with the 5-clique and ten 4-cliques
5. **Proving that execution paths exist** where the algorithm fails to find the maximum clique
6. **Demonstrating the non-determinism** is the fatal flaw

## Key Insight

The fundamental error is treating a **non-deterministic polynomial-time algorithm** as if it were deterministic. LaPlante's algorithm is essentially an NP algorithm (guess-and-check), not a P algorithm. The arbitrary choices in Phase 2 are analogous to non-deterministic guesses. Without backtracking (which would make it exponential) or a deterministic strategy for making correct choices (which LaPlante doesn't provide), the algorithm cannot reliably find the maximum clique.

## Lesson for P vs NP

This attempt illustrates a common pitfall in P vs NP proof attempts:
- **Heuristics work on many graphs** but fail on carefully constructed counterexamples
- **Polynomial-time per execution** ≠ **guaranteed polynomial-time solution**
- **Non-deterministic choices** without backtracking lead to incorrect results
- **Greedy/local strategies** often miss global optima in NP-complete problems

## References

1. M. LaPlante, "A Polynomial Time Algorithm For Solving Clique Problems," arXiv:1503.04794v1, March 2015.
2. H. A. Cardenas, C. Holtz, M. Janczak, P. Meyers, N. S. Potrepka, "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami," arXiv:1504.06890v1, April 2015.
3. G. Woeginger, "The P-versus-NP page," https://www.win.tue.nl/~gwoegi/P-versus-NP.htm

## Formalization Files

- `coq/LaPlante2015.v` - Coq formalization
- `lean/LaPlante2015.lean` - Lean 4 formalization
- `isabelle/LaPlante2015.thy` - Isabelle/HOL formalization
