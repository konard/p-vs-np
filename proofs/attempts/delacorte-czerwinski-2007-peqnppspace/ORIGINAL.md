# Original Papers: Graph Isomorphism Claims (2007)

This document contains the full text of both papers from attempt #41.

---

## Paper 1: Graph Isomorphism is PSPACE-complete

**Author**: Matthew Delacorte
**Date**: August 30, 2007
**ArXiv**: arXiv:0708.4075v1 [cs.CC]

### Abstract

Combining the results of A.R. Meyer and L.J. Stockmeyer "The Equivalence Problem for Regular Expressions with Squaring Requires Exponential Space", and K.S. Booth "Isomorphism testing for graphs, semigroups, and finite automata are polynomially equivalent problems" shows that graph isomorphism is PSPACE-complete.

### 1 Proof

The equivalence problem for regular expressions was shown to be PSPACE-complete by (Meyer and Stockmeyer [2]). Booth [1] has shown that isomorphism of finite automata is equivalent to graph isomorphism. Taking these two results together with the equivalence of regular expressions, right-linear grammars, and finite automata see [3] for example, shows that graph isomorphism is PSPACE-complete.

### References

[1] Booth, K.S. Isomorphism testing for graphs, semigroups, and finite automata are polynomially equivalent problems, SIAM J. Comput. 7, No 3, (1978), 273-279.

[2] Hopcroft, J.E., and Ullman, J.D. (1979), Introduction to Automata Theory, Languages and Computation, Addison-Wesley, Reading, MA.

[3] Meyer, A.R. and Stockmeyer, L.J. The Equivalence Problem for Regular Expressions with Squaring Requires Exponential Space, 13th Annual IEEE Symp. on Switching and Automata Theory, Oct., 1972, 125-129.

---

## Paper 2: Critique on "A Polynomial Time Algorithm for Graph Isomorphism"

**Author**: Reiner Czerwinski
**Date**: October 18, 2022 (retraction of November 2007 paper)
**ArXiv**: arXiv:0711.2010v5 [cs.CC]

### Abstract

In the paper "A Polynomial Time Algorithm for Graph Isomorphism" we claimed, that there is a polynomial algorithm to test if two graphs are isomorphic. But the algorithm is wrong. It only tests if the adjacency matrices of two graphs have the same eigenvalues. There is a counterexample of two non-isomorphic graphs with the same eigenvalues.

### 1 Introduction

Let A the adjacency matrix of G and A' the adjacency matrix of G'. G and G' are isomorphic if there is a permutation matrix P with A' = P * A * P^T. The adjacency matrices of isomorphic graphs have equal eigenvalues.

The algorithm described in [1] only tests if the graphs have the same eigenvalues. But unfortunately, there are non-isomorphic graphs with the same eigenvalues. In the next section we will show how to construct them.

### 2 Strongly Regular Graphs

Let G be a Graph. G ∈ SRG(n, k, a, c) if G is a k-connected graph with n vertices, where adjacent vertices have a common neighbours and non-adjacent vertices have c common neighbours. For further information see [2, chapter 10]. G is strongly regular if there are non-negative numbers n, k, a, c with G ∈ SRG(n, k, a, c).

**Theorem 1.** If G and G' are in SRG(n, k, a, c) then G and G' have the same eigenvalues.

A proof of this is shown in [2, page 219f].

#### 2.1 Counterexample

There are non-isomorphic graphs with the same eigenvalues. E.g. there are 180 pairwise non-isomorphic graphs in SRG(36, 14, 4, 6) [3].

### References

[1] Reiner Czerwinski. A polynomial time algorithm for graph isomorphism, 2008.

[2] Chris Godsil and Gordon F Royle. Algebraic graph theory, volume 207. Springer Science & Business Media, 2001.

[3] Brendan D McKay and Edward Spence. Classification of regular two-graphs on 36 and 38 vertices. Australasian Journal of Combinatorics, 24:293–300, 2001.

---

## Analysis

### Delacorte's Error

The fundamental error in Delacorte's paper is a **flawed chain of reasoning**:

1. ✓ Regular expression equivalence is PSPACE-complete (Meyer & Stockmeyer, 1972)
2. ✓ Regular expressions, right-linear grammars, and finite automata are equivalent (standard automata theory)
3. ✓ Graph isomorphism and finite automaton isomorphism are polynomial-time equivalent (Booth, 1978)
4. ✗ **Therefore, graph isomorphism is PSPACE-complete**

The error is that **equivalence** of objects (two automata accepting the same language) is a different problem from **isomorphism** of objects (two automata having the same structure). Booth's result shows that testing if two finite automata are structurally identical is polynomial-time equivalent to graph isomorphism. But the PSPACE-complete problem is testing if two regular expressions **accept the same language**, not if they are structurally isomorphic.

**Why this matters**:
- Isomorphism: "Do these two objects have the same structure?"
- Equivalence: "Do these two objects accept/recognize/define the same thing?"
- These are fundamentally different questions with different complexity.

### Czerwinski's Error

Czerwinski himself identified and documented the error in 2022:

**The algorithm only checks eigenvalue equality, but:**
- Isomorphic graphs always have the same eigenvalues ✓
- Graphs with the same eigenvalues are not always isomorphic ✗

**Counterexample**: There exist 180 pairwise non-isomorphic graphs in SRG(36, 14, 4, 6) that all share the same eigenvalue spectrum.

This means the algorithm gives **false positives** - it will claim graphs are isomorphic when they are not.

### Combined Claim

If both were correct:
- GI ∈ PSPACE-complete (Delacorte)
- GI ∈ P (Czerwinski)
- Therefore: P = PSPACE

This would be an extraordinary result, collapsing the polynomial hierarchy completely. The community consensus is that P ≠ PSPACE, making this result highly implausible.

### Current Status of Graph Isomorphism

As of 2024, the complexity status of graph isomorphism is:
- GI ∈ NP (easy to verify)
- GI ∈ co-AM (Goldreich, Micali, Wigderson, 1991)
- GI ∈ quasi-polynomial time (Babai, 2016): Time O(exp(log^c n))
- Not known to be NP-complete
- Not known to be in P
- Considered unlikely to be PSPACE-complete
