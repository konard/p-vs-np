# Original Paper: A Deterministic Polynomial-time Algorithm for the Clique Problem

**Author**: Zohreh O. Akbari
**Year**: 2008
**Title**: A Deterministic Polynomial-time Algorithm for the Clique Problem and the Equality of P and NP Complexity Classes
**Publication**: Proceedings of World Academy of Science, Engineering and Technology, Volume 35 (November 2008)
**Updated Version**: IEEE/ACIS 12th International Conference on Computer and Information Science (ICIS), 2013 - "A polynomial-time algorithm for the maximum clique problem"
**Claim**: P = NP via a deterministic polynomial-time algorithm for the NP-complete Clique Problem

## Abstract (Reconstructed from Available Information)

This paper claims to present a deterministic polynomial-time algorithm for solving the Maximum Clique Problem, one of Karp's original 21 NP-complete problems. Since the Clique Problem is NP-complete, the existence of such an algorithm would prove that P = NP.

## The Clique Problem

**Definition**: Given an undirected graph G = (V, E) and an integer k, determine whether there exists a clique (complete subgraph) of size at least k.

**Formal Statement**:
- Input: An undirected graph G = (V, E) where V is the set of vertices and E is the set of edges, and an integer k
- Question: Does there exist a subset S ⊆ V with |S| ≥ k such that for every pair of distinct vertices u, v ∈ S, the edge (u, v) ∈ E?

**Computational Complexity**:
- Proven NP-complete by Richard Karp in 1972
- Finding the maximum clique is also NP-hard
- No polynomial-time algorithm is known (unless P = NP)
- The problem remains hard even to approximate within certain factors

## Main Claim

The paper claims to provide a deterministic algorithm that solves the Clique Problem in polynomial time, thereby proving P = NP.

**Key Assertion**: The proposed algorithm can determine whether a graph G contains a clique of size k in time polynomial in the size of the graph.

**Implication**: Since the Clique Problem is NP-complete, any NP problem can be reduced to it in polynomial time. Therefore, a polynomial-time solution to the Clique Problem implies that all NP problems can be solved in polynomial time, proving P = NP.

## Logical Structure

The claim follows this valid logical chain:

1. **Premise 1**: The Clique Problem is NP-complete (Karp, 1972)
2. **Premise 2**: There exists a deterministic polynomial-time algorithm for the Clique Problem
3. **Inference**: If an NP-complete problem can be solved in polynomial time, then P = NP
4. **Conclusion**: P = NP

The logical structure is **correct**. The issue lies in whether Premise 2 is actually true.

## Why This Would Matter

If the claim were correct, it would:

1. **Resolve the P vs NP question**: One of the seven Millennium Prize Problems with a $1 million reward
2. **Revolutionize computer science**: Enable polynomial-time solutions to thousands of important problems
3. **Impact cryptography**: Many cryptographic systems rely on the assumption that P ≠ NP
4. **Affect optimization**: Enable efficient solutions to scheduling, routing, resource allocation, and many other practical problems

## Historical Context

### NP-Completeness of Clique

- **1972**: Richard Karp proves that the Clique Problem is NP-complete in his seminal paper "Reducibility Among Combinatorial Problems"
- **1999**: Johan Håstad proves strong inapproximability results for the Maximum Clique Problem
- **Ongoing**: The Clique Problem remains one of the most studied NP-complete problems

### Similar Attempts

Many researchers have attempted to solve P vs NP via the Clique Problem:

1. **Hamelin (2011)**: Claimed polynomial-time clique algorithm, but complexity was hidden in exponential clique membership bounds
2. **Dhami et al. (2014)**: Published a P = NP claim based on clique algorithms, later withdrawn after failures on large instances
3. **Cardenas et al. (2015)**: Provided refutations of clique-based approaches showing fundamental barriers

### Why Clique-Based Approaches Are Tempting

The Clique Problem has several properties that make it seem approachable:

1. **Simple Definition**: Easy to state and understand
2. **Clear Structure**: Complete subgraphs have obvious structural properties
3. **Local Checking**: Can verify if vertices form a clique in polynomial time
4. **Symmetry**: Cliques exhibit symmetries that seem exploitable

However, these same properties make it difficult to find efficient algorithms - the exponential number of potential cliques makes exhaustive search infeasible.

## Known Issues with the Approach

While the specific details of Akbari's algorithm are not widely available in accessible literature, clique-based P = NP attempts typically fail in one or more of the following ways:

### 1. Hidden Exponential Complexity

**Problem**: The algorithm appears polynomial when expressed in terms of certain parameters, but those parameters can be exponential in the input size.

**Example**: An algorithm with complexity O(n × C(G)) where C(G) is the number of cliques in graph G may appear polynomial, but C(G) can be as large as 2^n for n vertices.

### 2. Special Case Solutions

**Problem**: The algorithm works efficiently only on certain graph structures (e.g., planar graphs, sparse graphs, graphs with bounded treewidth).

**Issue**: NP-completeness requires worst-case polynomial time over ALL instances, not just special cases.

### 3. Incorrect Complexity Analysis

**Problem**: Failing to account for the true cost of operations within the algorithm.

**Common Mistakes**:
- Counting iterations without accounting for iteration cost
- Assuming expensive operations can be done in constant time
- Using average-case instead of worst-case analysis

### 4. Missing Correctness Proof

**Problem**: Even if an algorithm runs quickly, it must be proven correct for all inputs.

**Issue**: Many fast heuristics (like greedy algorithms) don't guarantee finding the maximum clique.

## References

1. **Karp, R. M.** (1972). "Reducibility Among Combinatorial Problems". In *Complexity of Computer Computations*, pp. 85–103.

2. **Håstad, J.** (1999). "Clique is hard to approximate within n^(1-ε)". *Acta Mathematica*, 182(1), 105-142.

3. **Woeginger, G. J.** "The P-versus-NP page" - Entry #49 (list of attempted P vs NP proofs)

4. **Original WASET Publication**: Akbari, Z. O. (2008). "A Deterministic Polynomial-time Algorithm for the Clique Problem and the Equality of P and NP Complexity Classes". *Proceedings of the World Academy of Science, Engineering and Technology*, Volume 35.

5. **Updated Version**: Akbari, Z. O. (2013). "A polynomial-time algorithm for the maximum clique problem". *IEEE/ACIS 12th International Conference on Computer and Information Science (ICIS)*.

---

**Note**: This document reconstructs the claims and context of the original paper based on available information. The original paper from WASET is not widely indexed in major academic databases. WASET (World Academy of Science, Engineering and Technology) has been identified by some academic organizations as a predatory publisher, which may explain the limited availability and peer review of this work.
