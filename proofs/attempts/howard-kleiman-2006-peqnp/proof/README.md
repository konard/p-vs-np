# Forward Proof Formalization: Kleiman 2006

This directory contains the formal proof attempt following Kleiman's approach as faithfully as possible.

## Contents

- `lean/KleimanProof.lean` - Lean 4 formalization
- `rocq/KleimanProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **The Jonker-Volgenannt Transformation**: Transform n×n asymmetric matrix M(a) into 2n×2n symmetric matrix M(s)
2. **Modified Floyd-Warshall Algorithm**: Application to the transformed symmetric matrix
3. **Acceptable Path Structure**: Paths alternating between non-zero and zero arcs
4. **Tour Extraction**: Claimed extraction of optimal tour from M(s) to M(a)
5. **Polynomial Time Claim**: O(n⁴) complexity assertion

## The Attempted Proof Logic

Kleiman's argument proceeds:

1. **Transform ATSP → Symmetric TSP**: Use Jonker-Volgenannt transformation to convert asymmetric cost matrix M(a) into symmetric matrix M(s)
2. **Apply Floyd-Warshall**: Use modified F-W algorithm to find shortest paths in M(s)
3. **Extract Tour**: Claim that the algorithm finds a minimal "acceptable cycle" in M(s) that yields optimal tour in M(a)
4. **Polynomial Complexity**: Assert O(n⁴) running time (O(n³) for F-W + O(n) backtracking factor)
5. **Conclusion**: Since ATSP is NP-hard and solvable in polynomial time, P = NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Kleiman's argument fails. These mark locations where:

1. **Floyd-Warshall vs TSP Gap**: The leap from shortest paths (which allow vertex revisits) to Hamiltonian cycles (visiting each vertex exactly once) is made without justification
2. **Acceptable Path Constraint**: The claim that "acceptable paths" preserve the Hamiltonian cycle constraint is assumed but not proven
3. **Complexity Analysis**: The O(n⁴) bound is asserted but doesn't account for the exponential number of possible vertex subsets that must be tracked
4. **Tour Extraction**: The extraction of an optimal tour from the Floyd-Warshall result assumes the algorithm solves a different problem than it actually does

## The Core Error

Floyd-Warshall solves the **all-pairs shortest path problem** with state space O(n³):
- State: (i, j, k) = shortest path from i to j using vertices {1,...,k}
- Allows vertex revisits
- Polynomial complexity

TSP requires solving the **Hamiltonian cycle problem** with state space O(n²·2ⁿ):
- State: (i, S) = shortest path ending at i having visited exactly vertices in set S
- Forbids vertex revisits (each visited exactly once)
- Exponential complexity

Matrix transformations cannot eliminate this fundamental gap between the two problem structures.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
