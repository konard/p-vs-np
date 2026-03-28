# Mohamed Mimouni (2006) - Original Proof Idea

## The Claim

Mohamed Mimouni claimed to prove **P = NP** by constructing a polynomial-time algorithm for the Clique Problem, which is NP-complete.

## Core Approach

### Step 1: Target the Clique Problem

The Clique Problem is a fundamental NP-complete problem proven by Karp in 1972.

**Problem Definition:**
- Given: An undirected graph G = (V, E) and an integer k
- Question: Does G contain a clique of size at least k?

A **clique** is a subset of vertices where every pair of vertices is connected by an edge (i.e., a complete subgraph).

### Step 2: Claim a Polynomial-Time Algorithm

Mimouni claimed to have constructed an algorithm that:
1. Takes as input a graph G and integer k
2. Returns YES if G contains a clique of size >= k, NO otherwise
3. Runs in polynomial time O(n^c) for some constant c

### Step 3: Conclude P = NP

Since the Clique Problem is NP-complete:
- If it can be solved in polynomial time, then P = NP
- This is because any NP problem can be reduced to Clique in polynomial time

## Why This Approach Seemed Promising

The Clique Problem has intuitive appeal for P=NP attempts because:

1. **Structural simplicity**: Cliques are well-understood mathematical objects
2. **Graph-based**: Many algorithms exist for graph problems, suggesting polynomial approaches might exist
3. **Local structure**: A clique can be verified locally, suggesting potential for efficient search

## The Fundamental Problems with Clique-Based Attempts

However, this approach consistently fails because:

### 1. Algorithm Works Only on Special Cases

The proposed algorithm might work on specific graph structures but fail on general instances:
- Dense graphs (many edges)
- Graphs with specific structure (trees, planar graphs)
- Small instances

But fail on:
- Sparse graphs with scattered cliques
- Adversarially constructed graphs
- Large general instances

**Key Principle**: A valid P=NP proof requires an algorithm that works for ALL instances, not just SOME instances.

### 2. Exponential Time Disguised as Polynomial

The algorithm appears polynomial in some parameter but is actually exponential in input size:
- O(n^k) time where k is the clique size is NOT polynomial in input size
- For k = log(n): O(n^(log n)) = O(2^((log n)^2)) - superpolynomial!
- For k as input: Runtime depends on k, not just graph size n

### 3. Incorrect Complexity Analysis

Errors in counting operations or analyzing loop iterations:
- Claiming nested loops are polynomial when they're actually exponential
- Miscounting recursive calls
- Ignoring the cost of subroutines

### 4. Incomplete Algorithm

The algorithm doesn't actually solve the problem correctly for all cases:
- Returns approximate solutions instead of exact answers
- Has correctness bugs that cause it to miss valid cliques or report false cliques

## Source Material Status

**Original Paper**: http://www.wbabin.net/science/mimouni.pdf (inaccessible as of 2026)
**Comments**: http://www.wbabin.net/comments/hofman.htm (inaccessible as of 2026)
**Language**: French

The original sources are no longer accessible. The domain (wbabin.net) is defunct and no archived versions could be found via Internet Archive or other archival services.

## What We Know From Historical Records

From Woeginger's P vs NP list (Entry #32):
- Author: Mohamed Mimouni
- Year: 2006 (August)
- Claim: P = NP
- Approach: Clique Problem algorithm
- Status: Comments were provided by Radoslaw Hofman (suggesting errors were identified)

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #32. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations, pp. 85-103.
3. Garey, M.R., Johnson, D.S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness." W.H. Freeman.
