# Finding Hamiltonian Cycle in Polynomial Time

**Authors:** Khadija Riaz, Malik Sikander Hayat Khiyal
**Publication:** Information Technology Journal, Volume 5, Issue 5, 2006, pages 851-859
**DOI:** 10.3923/itj.2006.851.859
**Publisher:** Asian Network for Scientific Information
**URL:** https://scialert.net/fulltext/?doi=itj.2006.851.859

---

## Abstract

The Hamiltonian Cycle (HC) problem is one of the well-known NP-complete problems. This paper presents an algorithm that aims to find Hamiltonian cycles in polynomial time. The approach uses preprocessing conditions and strategic node selection to minimize backtracking operations, claiming to reduce the problem's complexity from exponential to polynomial time.

---

## Introduction

The Hamiltonian Cycle problem asks whether a given graph contains a cycle that visits each vertex exactly once and returns to the starting vertex. This problem has been proven to be NP-complete, meaning no polynomial-time algorithm is currently known for solving it in the general case.

Traditional approaches to solving the HC problem involve exhaustive search through all possible paths, resulting in exponential time complexity. This paper proposes a different approach that uses:

1. Preprocessing conditions to eliminate impossible cases
2. Degree-based node selection strategies
3. Limited backtracking only at "junction nodes"

The authors claim that these techniques allow the problem to be solved in polynomial time.

---

## Preprocessing Phase

The algorithm begins with a preprocessing phase that applies the following conditions:

### Condition 1: Remove Parallel Edges and Self-Loops
- Remove all parallel edges (multiple edges between the same pair of vertices)
- Remove all self-loops (edges from a vertex to itself)

**Rationale:** A Hamiltonian cycle uses exactly one edge between any two vertices and does not revisit the same vertex.

### Condition 2: Reject Graphs with Degree-1 Nodes
- If any node has degree 1, reject the graph as it cannot contain a Hamiltonian cycle

**Rationale:** A Hamiltonian cycle requires each vertex to have at least two incident edges (one to enter, one to exit).

### Condition 3: Limit Adjacent Degree-2 Nodes
- If any node has more than two adjacent nodes with degree 2, reject the graph

**Rationale:** This condition is claimed to reduce the search space, though the formal justification is not fully developed in the paper.

---

## Processing Phase

The main algorithm proceeds as follows:

### Step 1: Select Starting Node
- Choose the node with the highest degree as the starting point
- This heuristic is based on the assumption that high-degree nodes are more likely to be part of a Hamiltonian cycle

### Step 2: Initialize Data Structures
- Create a stack to store adjacent nodes (for backtracking)
- Create a list to track visited edges
- Maintain a count of traversed vertices

### Step 3: Node Selection Strategy
The algorithm uses the following priority order for selecting the next node:

1. **Priority 1:** Select an unvisited adjacent node with the least degree
2. **Priority 2:** If multiple nodes have the same least degree, choose arbitrarily
3. **Priority 3:** Mark the traversed edge to prevent revisiting

**Rationale:** Selecting least-degree nodes first is intended to avoid leaving isolated vertices that cannot be included in the cycle.

### Step 4: Junction Nodes
- A "junction node" is defined as a node where the selection of the next node is ambiguous
- When encountering a junction node, store the alternative choices in the stack
- If a dead end is reached, backtrack to the most recent junction node and try an alternative

### Step 5: Cycle Completion
- Continue until all n vertices are visited
- Check if there is an edge from the current vertex back to the starting vertex
- If yes, a Hamiltonian cycle has been found
- If no, backtrack and try alternative paths

---

## Key Claims

### Claim 1: Polynomial-Time Complexity
The paper claims that the algorithm runs in polynomial time because:
- Preprocessing is clearly polynomial (O(n²) or O(m) where n = vertices, m = edges)
- The main processing phase is claimed to avoid exponential backtracking
- **Critical assertion:** "Backtracking occurs only at junction nodes, and the number of junction nodes is limited"

### Claim 2: Correctness
The algorithm is claimed to find a Hamiltonian cycle whenever one exists in the graph.

### Claim 3: Valid Selection Conditions
The paper asserts that the preprocessing conditions and selection strategies provide "valid conditions to decide the probability of HC exist."

---

## Algorithm Pseudocode (Reconstructed)

```
Algorithm: FindHamiltonianCycle(G)
Input: Graph G = (V, E)
Output: Hamiltonian cycle if one exists, or "No HC" otherwise

Preprocessing:
1. Remove parallel edges and self-loops from G
2. For each vertex v in V:
   - If degree(v) == 1: return "No HC"
   - If v has more than 2 adjacent vertices with degree 2: return "No HC"

Processing:
3. start ← vertex with maximum degree in V
4. current ← start
5. visited ← {start}
6. path ← [start]
7. junctionStack ← empty stack

8. While |visited| < |V|:
   a. neighbors ← unvisited adjacent vertices of current
   b. If neighbors is empty:
      - If junctionStack is empty: return "No HC"
      - (current, path, visited) ← pop from junctionStack
      - Continue to step 8
   c. If |neighbors| > 1:
      - Push (current, path, visited, neighbors[1:]) to junctionStack
   d. next ← neighbor with minimum degree from neighbors
   e. Add next to visited
   f. Append next to path
   g. current ← next

9. If edge (current, start) exists in E:
   - Return path + [start] as Hamiltonian cycle
10. Else:
   - If junctionStack is not empty:
      - Goto step 8.b (backtrack)
   - Return "No HC"
```

---

## Discussion

### Claimed Advantages
1. **Reduced backtracking:** The preprocessing conditions eliminate many impossible cases
2. **Strategic selection:** Degree-based heuristics guide the search toward successful paths
3. **Polynomial complexity:** The authors claim backtracking is limited to polynomial many operations

### Issues and Gaps
1. **Missing complexity proof:** The paper does not provide a rigorous mathematical proof that the algorithm runs in polynomial time
2. **Junction node analysis:** No formal analysis of how many junction nodes can exist in the worst case
3. **Correctness proof:** No formal proof that the algorithm finds a Hamiltonian cycle when one exists
4. **Counter-examples:** The paper does not address potential counter-examples where the greedy strategy might fail

---

## Conclusion

The paper presents a heuristic approach to the Hamiltonian Cycle problem that combines preprocessing, degree-based node selection, and limited backtracking. The authors claim this approach solves the problem in polynomial time, which would prove P = NP since HC is NP-complete.

However, the paper lacks:
- Rigorous time complexity analysis
- Formal correctness proofs
- Discussion of worst-case scenarios
- Engagement with the extensive literature on why greedy approaches to NP-complete problems typically fail

**Note:** This paper's claims have not been accepted by the theoretical computer science community, and the HC problem remains classified as NP-complete.

---

## References

1. Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*. W. H. Freeman.
2. Karp, R. M. (1972). "Reducibility Among Combinatorial Problems." In *Complexity of Computer Computations*, pp. 85-103.

---

## Metadata

**Journal:** Information Technology Journal
**Volume:** 5
**Issue:** 5
**Year:** 2006
**Pages:** 851-859
**ISSN:** 1812-5638
**Publisher:** Asian Network for Scientific Information
**Indexed:** Listed on Woeginger's P vs NP attempts list (Entry #38)

---

*This document is a reconstruction of the paper's content based on available information. For the complete original paper, please refer to the official publication.*
