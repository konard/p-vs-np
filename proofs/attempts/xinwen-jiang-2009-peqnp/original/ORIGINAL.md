# A Polynomial Time Algorithm for the Hamilton Circuit Problem

**Author**: Xinwen Jiang
**arXiv**: 1305.5976 [cs.CC]
**Submitted**: May 25, 2013 (v1), with earlier versions from 2009-2011

> *Note: This is a reconstruction of the key content from Jiang's arXiv paper (arXiv:1305.5976) for academic analysis purposes. The original paper is available at https://arxiv.org/abs/1305.5976. This reconstruction follows the paper's structure and presents its claims and arguments in English.*

---

## Abstract

This paper presents a polynomial time algorithm for the Hamilton Circuit problem.
The approach proceeds by:
1. Defining an intermediate problem called the Multistage Graph Simple Path (MSP) problem
2. Showing that the Hamilton Circuit problem can be polynomially reduced to the MSP problem
3. Providing a polynomial time algorithm for the MSP problem

Since Hamilton Circuit is NP-complete, this would establish P = NP.

---

## 1. Introduction

The P versus NP problem is one of the most important open problems in mathematics and computer science. This paper claims to resolve it in favor of P = NP by providing a polynomial-time algorithm for the Hamilton Circuit (HC) problem, which is a well-known NP-complete problem.

**The Hamiltonian Circuit Problem**: Given a directed graph G = (V, E), does G contain a directed Hamiltonian circuit, i.e., a directed cycle that passes through each vertex exactly once?

**Approach**: The paper introduces a new intermediate problem, the Multistage Graph Simple Path (MSP) problem, and reduces HC to MSP while claiming MSP is solvable in polynomial time.

---

## 2. The Multistage Graph Simple Path (MSP) Problem

### 2.1 Multistage Graph Definition

A **multistage graph** is a directed graph G = (V, E) where:
- The vertex set V is partitioned into k + 1 disjoint subsets: V₀, V₁, ..., Vₖ (stages)
- Each edge (u, v) ∈ E goes from some stage Vᵢ to the next stage Vᵢ₊₁

The paper uses a **labeled multistage graph** where vertices carry additional label information corresponding to vertices of the original HC instance.

### 2.2 MSP Problem Statement

**Given**: A multistage graph with labeled vertices, a source vertex s ∈ V₀, and a sink vertex t ∈ Vₖ

**Question**: Does there exist a simple path from s to t that:
1. Passes through exactly one vertex in each stage
2. Uses each label exactly once (each original vertex visited exactly once)

*Note*: The exact formal definition of the label constraint and what constitutes a "valid" MSP instance is not precisely stated in the paper — this vagueness is one of the main criticisms.

---

## 3. The Reduction: HC to MSP

### 3.1 Construction

Given a directed graph G = (V, E) with |V| = n vertices where we want to determine if a Hamiltonian circuit exists:

**Step 1**: Create a multistage graph M with n+1 stages V₀, V₁, ..., Vₙ

**Step 2**: At each stage Vᵢ (for i = 1, ..., n), include n nodes, one for each original vertex

**Step 3**: Add edges between stages: add edge from (i, u) to (i+1, v) if:
- Edge (u, v) exists in G
- Vertex v has not yet been used in the path leading to (i, u)

**Step 4**: The source is the starting vertex and the sink represents completing the circuit back to the start

### 3.2 Claimed Correctness of Reduction

**Claim**: Graph G has a Hamiltonian circuit if and only if the corresponding MSP instance has a valid simple path.

The paper asserts this correspondence but does not provide a rigorous proof of:
- Completeness: Every HC in G corresponds to a valid MSP path
- Soundness: Every valid MSP path corresponds to an HC in G

---

## 4. The Polynomial Algorithm for MSP

### 4.1 Algorithm Description

The paper claims to provide an algorithm for MSP that runs in polynomial time, based on a dynamic programming approach:

**State**: (stage i, current vertex u, set of visited labels)

*Note*: If the "set of visited labels" is tracked explicitly, this creates 2ⁿ possible states — exactly the exponential blowup of standard Held-Karp algorithm. The paper claims to avoid this, but does not rigorously explain how.

**Claimed Key Insight**: Due to the structure of the labeled multistage graph, the algorithm can determine at each stage which transitions are valid without tracking the full set of visited labels — allegedly reducing the state space to polynomial size.

**Algorithm Sketch** (as described in the paper):
1. Initialize: Start at source vertex in stage V₀
2. For each stage i from 0 to n-1:
   - For each valid current position:
     - Extend path to next stage
     - (Claim) Prune invalid extensions using local structure
3. Check if any path reaches the sink at stage Vₙ

### 4.2 Complexity Claim

The paper claims the algorithm runs in O(n³) or O(n⁴) time.

*Note*: No rigorous complexity analysis is provided. The claim relies on the assertion that state space pruning keeps the computation polynomial.

### 4.3 Experimental Validation

From later versions of the work (2014):
> "The MSP problem possesses a novel polynomial-time heuristic algorithm, which has undergone extensive test and always give the correct answer for all instances (more than 5 × 10⁷) generated up to now."

The author acknowledges: "Although there is no broad consensus with proving the correctness of the polynomial-time heuristic algorithm for the MSP problem."

---

## 5. Conclusion

The paper concludes:

1. The HC problem polynomially reduces to the MSP problem
2. The MSP problem has a polynomial-time algorithm
3. Therefore, HC ∈ P
4. Since HC is NP-complete, P = NP

---

## 6. Community Reception and Critiques

### Hacker News Discussion (June 2013, item #5785693)

When the paper was posted on Hacker News, key criticisms included:

**Critique 1 — Formalization**:
> "The problem could likely be formalized in a more effective way"
The MSP problem definition is not precise enough to verify the claimed reduction.

**Critique 2 — Possible Wrong Complexity Class**:
> "Jiang's labelled multistage graphs correspond to partially ordered sets, and finding Hamiltonian cycles in their comparability graphs is known not to be NP-complete."
If the MSP problem is actually in P (not NP-complete), then the reduction from HC to MSP does not establish HC ∈ P.

**Critique 3 — Red Flags**:
- The paper does not use standard mathematical typesetting
- Heavy self-citation
- Multiple revisions over many years without peer-reviewed publication
- References to Scott Aaronson's checklist for false P=NP claims

**Critique 4 — Experimental vs Mathematical**:
Testing millions of instances cannot constitute a mathematical proof.

### Academic Reception

The paper has not been:
- Published in a peer-reviewed journal or conference
- Accepted by the theoretical computer science community
- Cited positively by complexity theorists

The paper has been on arXiv since 2013 without generating a formal published refutation, which itself suggests the community considers the errors sufficiently obvious.

---

## References (from original paper)

1. Jiang, X. (earlier version, Chinese journal, 2007)
2. Jiang, X. (2009 version, unpublished)
3. Jiang, X. (2010 version, unpublished)
4. Jiang, X. (2011 version, unpublished)
5. Jiang, X. (2013). arXiv:1305.5976
6. [Author's blog, trytoprovenpvsp.blog.sohu.com]
7. [Various self-citations to earlier personal work]

*Note: The heavy reliance on self-citation (~10 out of ~12 references) is itself a red flag for the reliability of the work, as it suggests lack of engagement with the broader research community.*
