# Howard Kleiman (2006) - P=NP via Modified Floyd-Warshall Algorithm for ATSP

**Attempt ID**: 37 (from Woeginger's list)
**Author**: Howard Kleiman
**Year**: 2006 (December)
**Claim**: P = NP
**Status**: Refuted

## Summary

In December 2006, Howard Kleiman proposed a polynomial-time algorithm for the Asymmetric Traveling Salesman Problem (ATSP) using a modified Floyd-Warshall algorithm. The argument was that if ATSP (an NP-hard problem) can be solved in polynomial time, this would prove P = NP.

## Main Argument

### The Approach

1. **Matrix Transformation**: Building on work by Jonker and Volgenannt, transform an n×n asymmetric cost matrix M(a) into a 2n×2n symmetric cost matrix M(s) with special structural properties
2. **Modified Floyd-Warshall**: Apply a modified Floyd-Warshall algorithm to the symmetric matrix M(s)
3. **Tour Extraction**: Extract an optimal tour in M(a) from the optimal tour in M(s)
4. **Polynomial Time**: The algorithm runs in at most O(n⁴) time, which is polynomial
5. **P=NP Conclusion**: Since ATSP is NP-hard, solving it in polynomial time would prove P = NP

### Key Technical Claim

The crucial claim was that:
- The transformation from M(a) to M(s) preserves optimality: "an optimal tour in M(s) yields an optimal tour in M(a)"
- The modified Floyd-Warshall algorithm can find an optimal tour in M(s) in polynomial time
- Therefore, we can solve ATSP in polynomial time

### Stated Complexity

The paper claims a time complexity of **O(n⁴)**, which is polynomial in the size of the problem.

## The Error

### Fundamental Flaw: Floyd-Warshall Solves a Different Problem

**The Error**: The Floyd-Warshall algorithm solves the **all-pairs shortest path problem**, not the **Traveling Salesman Problem**.

**Why This Matters**:
- **Floyd-Warshall** finds the shortest path between every pair of vertices
- **TSP** finds the shortest path that visits every vertex exactly once and returns to the start
- These are fundamentally different problems with different constraints

### The Critical Distinction

#### What Floyd-Warshall Does:
- Input: Weighted graph
- Output: Shortest distance between every pair of vertices
- Constraint: Find the minimum-weight path (may reuse vertices and edges)
- Complexity: O(n³)
- Problem Class: Polynomial time (in P)

#### What TSP Requires:
- Input: Weighted graph
- Output: Shortest tour visiting all vertices exactly once
- Constraint: Must visit each vertex exactly once (Hamiltonian cycle)
- Complexity: O(2^n) with dynamic programming, O(n!) with brute force
- Problem Class: NP-hard

### Why the Approach Cannot Work

1. **Different Constraints**: Floyd-Warshall allows paths that revisit vertices; TSP forbids this
2. **Exponential Subproblems**: TSP has exponentially many valid tours to consider
3. **Hamiltonian Cycle Requirement**: Ensuring each vertex is visited exactly once is the hard part that makes TSP NP-hard
4. **Matrix Transformation Insufficient**: Simply transforming the cost matrix does not change the fundamental complexity of the problem

### The Subproblem Structure

- **Floyd-Warshall subproblems**: "What is the shortest path from i to j using vertices {1,...,k}?" - **Polynomial** number of subproblems: O(n³)
- **TSP subproblems**: "What is the shortest path from i to j visiting exactly the vertices in set S?" - **Exponential** number of subproblems: O(n²·2^n)

The key difference is that TSP must track which vertices have been visited, leading to exponentially many subproblems.

## Why This Approach Is Tempting

The approach is appealing because:
- Floyd-Warshall IS efficient (O(n³))
- It DOES find shortest paths in graphs
- Matrix transformations CAN sometimes preserve problem structure
- The ATSP is related to finding shortest paths

However, the Hamiltonian cycle constraint (visiting each vertex exactly once) is what makes TSP hard, and this constraint cannot be efficiently handled by shortest-path algorithms.

## Broader Context

### The Shortest Path vs. Hamiltonian Cycle Gap

This is a fundamental distinction in graph theory:
- **Shortest Path Problems** (like Floyd-Warshall, Dijkstra, Bellman-Ford): Polynomial time
- **Hamiltonian Cycle Problems** (like TSP): NP-hard

The difference is the "exactly once" constraint. Checking if a graph has a Hamiltonian cycle is itself NP-complete, which is why TSP is hard.

### Dynamic Programming and TSP

Dynamic programming CAN solve TSP, but not in polynomial time:
- The Held-Karp algorithm solves TSP in O(n²·2^n) time using dynamic programming
- This is better than brute force O(n!) but still exponential
- The exponential factor comes from tracking which vertices have been visited

### Why Modifications Don't Help

Simply "modifying" Floyd-Warshall cannot overcome this fundamental barrier:
- To solve TSP, you MUST track which vertices have been visited
- This inherently creates an exponential number of states
- Any polynomial algorithm that doesn't track visited vertices cannot ensure the "exactly once" constraint

## The Unproven Assumption

The paper's claim rests on an unproven (and false) assumption:

**Assumption**: "Due to the structure of M(s), we can always obtain an optimal tour in M(a) in polynomial time."

**Reality**: The structure of M(s) does not eliminate the need to enforce the Hamiltonian cycle constraint, which requires exponential time.

## Key Lessons

1. **Algorithm Purpose Matters**: Using an algorithm designed for one problem (shortest paths) on a different problem (Hamiltonian cycles) does not work
2. **Constraints Are Critical**: The "visit exactly once" constraint is what makes TSP hard
3. **Polynomial Reductions Go One Way**: We can reduce TSP to shortest paths with exponential overhead, but not with polynomial overhead
4. **Matrix Transformations Have Limits**: Transforming the input representation does not change the fundamental complexity class
5. **DP Is Not Magic**: Dynamic programming can improve complexity, but cannot turn exponential problems into polynomial ones without structural changes

## Formalization Goals

In this directory, we formalize:

1. **The Floyd-Warshall Algorithm**: What it computes (all-pairs shortest paths)
2. **The TSP Problem**: What it requires (Hamiltonian cycle with minimum weight)
3. **The Critical Difference**: Why shortest path ≠ Hamiltonian cycle
4. **The Complexity Gap**: Why O(n³) cannot solve a problem with 2^n subproblems
5. **The Failure Point**: Where Kleiman's argument breaks down

The formalization demonstrates that:
- Floyd-Warshall solves all-pairs shortest paths in O(n³)
- TSP requires tracking exponentially many visited-vertex sets
- No polynomial-time reduction can bridge this gap
- Therefore, the claimed polynomial-time algorithm for TSP is invalid

## References

### Primary Sources

- **Original Claim**: Kleiman, H. (2006). "The Asymmetric Traveling Salesman Problem"
  - arXiv:math.CO/0612114
  - Submitted: December 5, 2006; Last revised: December 9, 2006
  - Available at: http://arxiv.org/abs/math.CO/0612114

### Related Work by Kleiman

- Kleiman, H. (2005). "The Symmetric Traveling Salesman Problem"
  - arXiv:math/0508212
- Kleiman, H. (2011). "The General Traveling Salesman Problem"
  - arXiv:1110.4052
- Kleiman, H. (2001). "The Floyd-Warshall Algorithm, the AP and the TSP"
  - arXiv:math/0111309

### Context

- **Woeginger's List**: Entry #37
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Background on Floyd-Warshall and TSP

- **Floyd-Warshall Algorithm**: Finds all-pairs shortest paths in O(n³)
- **Held-Karp Algorithm**: Solves TSP in O(n²·2^n) using dynamic programming
- **TSP Complexity**: Known to be NP-hard since Karp's 1972 paper
- **Hamiltonian Cycle**: Deciding if a Hamiltonian cycle exists is NP-complete

## Key Insights

### Why P ≠ NP Is Plausible

This attempt illustrates why many complexity theorists believe P ≠ NP:
- There is a fundamental gap between problems with polynomial structure (like shortest paths) and problems with exponential structure (like Hamiltonian cycles)
- Many different approaches to solving NP-hard problems in polynomial time have been tried and all have failed
- The exponential explosion in the number of valid solutions/states seems inherent to these problems

### The "Visit Exactly Once" Barrier

The core difficulty in TSP is enforcing the constraint that each vertex is visited exactly once. This constraint:
- Is easy to verify (polynomial time)
- Is hard to ensure in construction (exponential time)
- Creates an exponential branching structure in any search or dynamic programming approach
- Cannot be eliminated by matrix transformations or algorithm modifications

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches to P vs NP
- [Repository README](../../../README.md) - Overview of the P vs NP problem
