# Original Attempt Description

## Source

US Patent Application 20080071849A1 filed by Cynthia Ann Harlan Krieger and Lee K. Jones in 2008.

## Core Idea

The authors claimed to have developed a polynomial-time algorithm for detecting Hamiltonian circuits in undirected graphs using matrix operations and projection matrices.

### The Approach

1. **Problem**: Detect whether an undirected graph contains a Hamiltonian circuit (a cycle visiting each vertex exactly once)
2. **Significance**: The Hamiltonian circuit problem is NP-complete, so a polynomial-time solution would prove P = NP
3. **Proposed Method**:
   - Represent the input graph as an adjacency matrix
   - Create a reference matrix with a known Hamiltonian circuit (e.g., a "clock-face" graph)
   - Form a projection matrix using matrix multiplication
   - Apply the projection to the input graph
   - Use QR decomposition and rank comparison to determine if a Hamiltonian circuit exists

### Claimed Complexity

The patent claimed O(n³) polynomial time complexity based on:
- Matrix multiplication operations
- QR decomposition
- Rank computation

### The Claim

The inventors claimed: "With this polynomial running time calculation result given for detecting the presence of a Hamiltonian circuit in an undirected graph, it has been shown that P equals any known NP problem or NP."

## Files in This Directory

- **README.md** (this file) - Description of the proof idea
- **ORIGINAL.md** - Complete conversion of the patent application to markdown (English)
- **ORIGINAL.pdf** - Download stub for the original patent application PDF

## Status

The patent application was published on March 20, 2008, but was later abandoned. The claim has not been validated by the theoretical computer science community, and P vs NP remains an open problem.

## Why This Matters

If valid, this would solve one of the seven Millennium Prize Problems and fundamentally change our understanding of computational complexity. However, the algorithm as described in the patent has not been verified to correctly solve the Hamiltonian circuit problem in all cases.
