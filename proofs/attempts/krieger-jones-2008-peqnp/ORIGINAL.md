# US Patent Application 20080071849A1

## Polynomial Method for Detecting a Hamiltonian Circuit

**Publication Number**: US20080071849A1
**Filing Date**: September 17, 2007
**Publication Date**: March 20, 2008
**Inventor**: Cynthia Ann Harlan Krieger
**Application Number**: US11/898,928
**Based on Provisional**: No. 60/844,680 (filed September 15, 2006)

---

## Abstract

An algorithm to determine the existence of a Hamiltonian circuit in an undirected graph. Hamiltonian circuit detection is classified as a class NP-complete problem. This algorithm tests whether a Hamiltonian circuit (a closed path through a graph that visits each and every node exactly one time) exists for a given graph. The running time calculation result of this algorithm is polynomial.

One way to process graphs using computer algorithms is to represent the graph as a matrix. Specifically, an adjacency matrix representation can be constructed such that rows and columns each equal a count of vertices where elements of the matrix are indexed by vertex pairs.

With this polynomial running time calculation result given for detecting the presence of a Hamiltonian circuit in an undirected graph, it has been shown that P equals any known NP problem or NP.

---

## Background

### Field of Invention

This invention relates to algorithms for detecting Hamiltonian circuits in undirected graphs and the implications for computational complexity theory.

### Description of Related Art

The Hamiltonian circuit problem is one of the most studied problems in computer science and discrete mathematics. It asks whether a given undirected graph contains a cycle that visits each vertex exactly once. This problem is known to be NP-complete, meaning that it is among the hardest problems in the complexity class NP.

The P versus NP question is one of the most important open problems in computer science and mathematics. It asks whether every problem whose solution can be quickly verified (NP) can also be quickly solved (P). A polynomial-time algorithm for any NP-complete problem would prove P=NP.

---

## Summary of Invention

This invention provides a method, computer-readable medium, and system for determining whether an undirected graph contains a Hamiltonian circuit in polynomial time. The method uses matrix operations including:

1. Adjacency matrix representation of the input graph
2. Construction of a reference matrix with a known Hamiltonian circuit (clock-face graph)
3. Formation of a projection matrix using matrix multiplication
4. Application of the projection to the input graph
5. Self-consistency testing using QR decomposition and rank comparison

The algorithm claims to determine the presence or absence of a Hamiltonian circuit in polynomial time, which would have significant implications for the P vs NP problem.

---

## Detailed Description

### Algorithm Steps

**Step 1: Validate Input**
- Verify the adjacency matrix is square (n×n)
- Verify all elements are binary (0 or 1)
- Verify the matrix is symmetric (for undirected graphs)

**Step 2: Create Reference Matrix**
- Construct a reference adjacency matrix A representing a graph with a known Hamiltonian circuit
- Example: Use a "clock-face" graph where vertices form a simple cycle: 1-2-3-...-n-1

**Step 3: Form Projection Matrix**
- Calculate P = (A^T) · A where A^T is the transpose of A
- This projection matrix is used to test the input graph

**Step 4: Apply Projection**
- Given input adjacency matrix X
- Calculate PX = P · X

**Step 5: Self-Consistency Testing**
- Perform QR decomposition on both PX and X
- Compare rank(PX) with rank(X)
- Check for repeated values in QR auxiliary matrices

**Step 6: Determine Result**
- If rank(PX) < rank(X): No Hamiltonian circuit exists
- If rank(PX) = rank(X) and no repeated QR values: Hamiltonian circuit exists
- Otherwise: Result inconclusive

### Complexity Analysis

The patent claims polynomial time complexity based on:
- Matrix multiplication: O(n³) operations
- QR decomposition: O(n³) operations
- Rank computation: O(n³) operations
- Total: O(n³) polynomial time

---

## Claims

### Claim 1
A method for determining whether an undirected graph contains a Hamiltonian circuit, comprising:
- Representing the graph as an adjacency matrix
- Creating a reference matrix with known Hamiltonian circuit
- Computing projection matrix from reference matrix
- Applying projection to input matrix
- Performing self-consistency test via QR decomposition
- Determining presence/absence based on rank comparison

### Claim 2
A computer-readable medium containing executable instructions that, when executed, perform the method of Claim 1.

### Claim 3
A system comprising a CPU, memory, and I/O configured to execute the algorithm described in Claim 1.

---

## Applications

The patent application lists potential applications including:
- Network design and optimization
- Logistics and routing problems
- Cryptography and encryption systems
- Integer factorization
- Boolean satisfiability (SAT) problems
- General NP-complete problem solving

---

## Status

**Abandoned**: This patent application was abandoned in 2011 due to failure to respond to USPTO office actions.

The theoretical computer science community has not validated this claimed P=NP proof. The Clay Mathematics Institute's Millennium Prize for P vs NP remains unclaimed, and the problem is still considered open as of 2026.

---

*Note: This is a summary and partial reconstruction of the patent text. For the complete official document, refer to Google Patents or USPTO records.*
