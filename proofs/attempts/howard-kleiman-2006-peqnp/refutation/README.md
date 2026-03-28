# Howard Kleiman (2006) - Refutation

## Why the Proof Fails

Kleiman's 2006 P=NP attempt contains a fundamental error: **Floyd-Warshall solves a different problem than TSP**.

## The Fatal Error: Algorithm Mismatch

### The Claim

Kleiman claimed that a modified Floyd-Warshall algorithm can solve ATSP in polynomial time O(n⁴).

### The Problem

**Floyd-Warshall** and **TSP** are fundamentally different problems:

| Aspect | Floyd-Warshall | TSP |
|--------|----------------|-----|
| **Problem** | All-pairs shortest paths | Hamiltonian cycle |
| **Constraint** | Allows revisiting vertices | Must visit each vertex exactly once |
| **Subproblems** | O(n³) polynomial | O(n²·2ⁿ) exponential |
| **Complexity** | O(n³) polynomial time | NP-hard |
| **Class** | P | NP-complete |

### Why This Is Fatal

1. **Different Constraints**: Floyd-Warshall finds shortest paths where vertices CAN be revisited; TSP requires visiting each vertex EXACTLY ONCE
2. **Exponential State Space**: TSP must track which vertices have been visited, creating 2ⁿ possible states
3. **Matrix Transformations Don't Help**: Transforming the cost matrix doesn't eliminate the exponential complexity of the Hamiltonian cycle constraint

## The Subproblem Structure Gap

### Floyd-Warshall Subproblems

State: `(i, j, k)` - "What is the shortest path from i to j using only vertices {1, 2, ..., k}?"

**Number of subproblems**: n × n × n = **O(n³)** - polynomial

### TSP (Held-Karp) Subproblems

State: `(i, S)` - "What is the shortest path ending at vertex i, having visited exactly the vertices in set S?"

**Number of subproblems**: n × 2ⁿ = **O(n · 2ⁿ)** - exponential

The set S can be any subset of n vertices, giving 2ⁿ possible states per ending vertex.

## Concrete Example

For n = 15 cities:
- **Floyd-Warshall**: 15 × 15 × 15 = **3,375 subproblems**
- **TSP**: 15 × 2¹⁵ = 15 × 32,768 = **491,520 subproblems**

The gap grows exponentially with n.

## Why the "Visit Exactly Once" Constraint Is Hard

The constraint that each vertex must be visited exactly once is what makes TSP NP-hard:

1. **Easy to Verify**: Given a tour, checking if it visits each vertex exactly once takes O(n) time
2. **Hard to Construct**: Finding such a tour requires considering exponentially many possibilities
3. **Cannot Be Relaxed**: Allowing revisits changes the problem to shortest paths (polynomial time)
4. **Cannot Be Bypassed**: Any correct TSP algorithm must enforce this constraint

## The Unproven Assumption

Kleiman's proof rests on this unproven claim:

> "Due to the special structure of M(s), an optimal tour in M(s) yields an optimal tour in M(a)."

**Reality**: The structure of M(s) does not eliminate the need to track which vertices have been visited, which inherently requires exponential time.

## The Shortest Path vs. Hamiltonian Cycle Barrier

This represents a fundamental divide in computational complexity:

### Shortest Path Problems (Polynomial - in P)
- Dijkstra's algorithm: O(E + V log V)
- Bellman-Ford: O(VE)
- Floyd-Warshall: O(V³)
- **All vertices can be revisited**

### Hamiltonian Cycle Problems (Exponential - NP-complete)
- Hamiltonian Path: NP-complete
- Hamiltonian Cycle: NP-complete
- TSP: NP-hard
- **Each vertex visited exactly once**

The "exactly once" constraint creates an exponential explosion in complexity that cannot be overcome by matrix transformations or algorithm modifications.

## Mathematical Foundation

### Why DP Doesn't Make TSP Polynomial

Dynamic programming CAN solve TSP, but not in polynomial time:
- **Held-Karp Algorithm**: Solves TSP in O(n²·2ⁿ) time
- Still exponential due to tracking visited vertices
- This is better than brute force O(n!) but not polynomial
- The 2ⁿ factor is unavoidable without violating the "exactly once" constraint

### The State Explosion

To correctly solve TSP, an algorithm must:
1. Track which vertices have been visited
2. Ensure no vertex is visited twice
3. Ensure all vertices are visited

This requires maintaining 2ⁿ different states (one for each subset of visited vertices), leading to exponential complexity.

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`revisit_vs_exactlyonce_different`**: Floyd-Warshall allows revisits; TSP forbids them
2. **`tsp_exponentially_more_subproblems`**: TSP has exponentially more subproblems than Floyd-Warshall
3. **`kleiman_approach_cannot_work`**: Matrix transformations cannot eliminate the exponential complexity

## Key Lessons

1. **Algorithm Purpose Matters**: An algorithm designed for one problem (shortest paths) cannot solve a fundamentally different problem (Hamiltonian cycles)
2. **Constraints Define Complexity**: The "visit exactly once" constraint is what makes TSP hard
3. **Input Transformations Have Limits**: Transforming the input representation doesn't change the fundamental complexity class
4. **DP Is Not Magic**: Dynamic programming improves complexity but cannot turn exponential problems into polynomial ones

## The P vs NP Gap

This attempt illustrates why P ≠ NP is widely believed:
- There is a fundamental gap between polynomial-structure problems (shortest paths) and exponential-structure problems (Hamiltonian cycles)
- The exponential explosion in the number of states seems inherent to NP-hard problems
- Many different approaches have been tried, and all have failed at this same barrier

## References

- **Kleiman, H.** (2006). "The Asymmetric Traveling Salesman Problem". arXiv:math.CO/0612114
- **Floyd, R. W.** (1962). "Algorithm 97: Shortest path"
- **Held, M., & Karp, R. M.** (1962). "A dynamic programming approach to sequencing problems"
- **Karp, R. M.** (1972). "Reducibility among combinatorial problems"
- **Woeginger's List**: Entry #37 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
