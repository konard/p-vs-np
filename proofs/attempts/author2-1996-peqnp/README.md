# Plotnikov (1996) - P=NP via Polynomial-Time Clique Partition

**Attempt ID**: 2
**Author**: Anatoly Plotnikov
**Year**: 1996
**Claim**: P=NP
**Source**: SouthWest Journal of Pure and Applied Mathematics (SWJPAM), Volume 1, 1996, pp. 16-29
**Title**: "Polynomial-Time Partition of a Graph into Cliques"

## Summary

Ukrainian mathematician Anatoly Plotnikov published a paper in 1996 claiming to provide a polynomial-time algorithm for partitioning an arbitrary undirected graph into the minimum number of cliques. Since the clique partition problem (also known as the minimum clique cover problem) is NP-complete, such an algorithm would imply P=NP.

## The Main Argument

Plotnikov's approach can be summarized as follows:

1. **Problem**: Given an undirected graph G = (V, E), partition the vertices into the minimum number of cliques (complete subgraphs).

2. **Claim**: The paper presents an O(n^5) algorithm that solves this problem optimally, where n is the number of vertices.

3. **Method**: The algorithm uses properties of finite partially ordered sets (posets) to find the solution to the partition problem.

4. **Implication**: Since the minimum clique cover problem is NP-complete, a polynomial-time algorithm for it would prove P=NP.

## Background: Why Clique Partition is NP-Complete

### The Clique Partition Problem

- **Input**: An undirected graph G = (V, E)
- **Output**: A partition of V into the minimum number of cliques

### Relationship to Graph Coloring

The clique partition problem is closely related to the graph coloring problem:
- A clique cover of graph G corresponds to a proper coloring of the complement graph Ḡ
- The minimum clique cover number χ̄(G) equals the chromatic number χ(Ḡ)
- Since graph coloring is NP-complete, so is clique partition

### Known Complexity Results

1. The decision version ("Can G be partitioned into k or fewer cliques?") is NP-complete
2. The optimization version is NP-hard
3. No polynomial-time algorithm is known unless P=NP
4. Approximation algorithms exist for special graph classes

## The Error in the Proof

The critical flaw in Plotnikov's proof likely falls into one of these common categories:

### Type 1: Hidden Exponential Complexity

**Most Likely Error**: The algorithm may appear polynomial at first glance, but upon careful analysis, some step has hidden exponential complexity. Common issues include:

- **Unbounded iteration**: A loop that appears to run polynomially many times but actually requires exponential iterations in worst cases
- **Subproblem explosion**: Recursive calls or dynamic programming with an exponential number of distinct subproblems
- **Combinatorial explosion**: Enumeration over structures (like poset chains or antichains) that grow exponentially

### Type 2: Incorrect Problem Reduction

**Possible Error**: The algorithm may solve a related but different problem:

- Solving an approximate version (finding a clique partition, but not necessarily minimal)
- Solving a restricted version (works only for special graph classes like chordal graphs)
- Solving a relaxed version (allowing overlapping cliques or covering instead of partitioning)

### Type 3: Circular Logic or Unproven Lemma

**Possible Error**: The proof may rely on:

- A lemma that assumes what needs to be proven
- A property of posets that only holds when the optimal solution is already known
- An oracle or subroutine that itself requires solving an NP-hard problem

### Type 4: Incomplete Case Analysis

**Possible Error**: The algorithm may:

- Handle only certain graph structures correctly
- Fail to cover all possible configurations in the case analysis
- Make implicit assumptions about graph properties (e.g., connectivity, regularity)

## Formalization Strategy

To identify the exact error, we formalize the proof in three theorem provers:

### 1. Coq (`coq/` directory)
- Define graphs, cliques, and partitions
- Formalize the poset-based algorithm
- Prove correctness (if possible) or identify where the proof fails
- Show the complexity bound

### 2. Lean (`lean/` directory)
- Use Mathlib's graph theory library
- Define the clique partition problem
- Implement Plotnikov's algorithm
- Attempt to prove polynomial-time complexity

### 3. Isabelle (`isabelle/` directory)
- Use Isabelle's graph theory and complexity frameworks
- Formalize the algorithm step-by-step
- Use sledgehammer to find gaps in the proof

## Expected Outcome

By formalizing Plotnikov's algorithm, we expect to:

1. **Identify the exact step** where the proof fails
2. **Classify the error** according to the types above
3. **Construct a counterexample** if the algorithm is incorrect
4. **Show the complexity gap** if the algorithm is exponential rather than polynomial

## References

1. **Original Paper**: Plotnikov, A. (1996). "Polynomial-Time Partition of a Graph into Cliques." *SouthWest Journal of Pure and Applied Mathematics*, Vol. 1, pp. 16-29.

2. **Woeginger's List**: Entry #2 on Gerhard Woeginger's "The P-versus-NP page"
   https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

3. **Clique Cover Problem**:
   - Wikipedia: https://en.wikipedia.org/wiki/Clique_cover
   - NP-completeness proof via reduction from graph coloring

4. **Related Work**:
   - Polynomial algorithms exist for special cases (chordal graphs, interval graphs)
   - Approximation algorithms with various guarantees
   - Parameterized complexity results

## Status

- [ ] Coq formalization in progress
- [ ] Lean formalization in progress
- [ ] Isabelle formalization in progress
- [ ] Error identified and documented
- [ ] Counterexample constructed (if applicable)

## Notes

Since the original 1996 paper is difficult to access, this formalization is based on:
- The problem statement (minimum clique partition)
- The claimed complexity (O(n^5))
- The described method (using poset properties)
- General knowledge of NP-completeness of clique partition

The formalization will reveal where the polynomial-time claim breaks down, even without access to every detail of the original argument.
