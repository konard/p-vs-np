# Zohreh O. Akbari (2008) - P=NP via Polynomial-Time Clique Algorithm

**Attempt ID**: 49 (from Woeginger's list)
**Author**: Zohreh O. Akbari
**Year**: 2008
**Claim**: P = NP
**Status**: Refuted

## Summary

In November 2008, Zohreh O. Akbari claimed to prove P = NP by designing "a deterministic polynomial time algorithm for the NP-hard clique problem." The work appeared in Volume 35 of the Proceedings of World Academy of Science, Engineering and Technology (WASET) under the title "A Deterministic Polynomial-time Algorithm for the Clique Problem and the Equality of P and NP Complexity Classes."

An updated version was later presented at the 2013 IEEE/ACIS 12th International Conference on Computer and Information Science (ICIS) with the title "A polynomial-time algorithm for the maximum clique problem."

## Main Argument

### The Approach

1. **Target Problem**: The Maximum Clique Problem - finding the largest complete subgraph in a given graph
2. **Claimed Algorithm**: A deterministic polynomial-time algorithm for solving the clique problem
3. **Implication**: Since the clique problem is NP-complete (proven by Karp, 1972), a polynomial-time algorithm would prove P = NP
4. **Conclusion**: The existence of such an algorithm demonstrates P = NP

### The Clique Problem

**Definition**: Given an undirected graph G = (V, E) and an integer k, the clique decision problem asks whether there exists a subset S ⊆ V of size at least k such that every pair of vertices in S is connected by an edge.

**Computational Significance**:
- Proven NP-complete by Richard Karp in 1972
- One of Karp's original 21 NP-complete problems
- Finding maximum cliques has applications in social network analysis, bioinformatics, coding theory, and many other fields
- No known polynomial-time algorithm exists (unless P = NP)

### Why This Would Imply P = NP

The reasoning chain is straightforward:
1. The clique problem is NP-complete
2. By definition, every NP problem can be reduced to any NP-complete problem in polynomial time
3. If we can solve the clique problem in polynomial time, we can solve ALL NP problems in polynomial time
4. Therefore, P = NP

This logic is **correct** - the issue is not with the implication, but with whether the proposed algorithm actually works.

## The Error in the Proof

While the specific technical details of Akbari's algorithm are not widely available in readily accessible literature, clique-based P = NP attempts typically fail in one or more of the following ways:

### Common Errors in Clique-Based P=NP Attempts

#### 1. Algorithm Only Works on Special Cases

**The Problem**: Many proposed algorithms work efficiently on specific graph structures (e.g., planar graphs, sparse graphs, graphs with bounded treewidth) but fail on general graphs.

**Why This Fails**:
- NP-completeness is defined in terms of worst-case complexity over ALL instances
- An algorithm that works on "most" graphs or "special cases" doesn't prove P = NP
- The hard instances of NP-complete problems are specifically constructed to be difficult

**Formal Issue**: The claim requires ∀G (algorithm solves G in polynomial time), but the proof only establishes ∃G₁, G₂, ... (algorithm solves these specific graphs in polynomial time).

#### 2. Hidden Exponential Complexity

**The Problem**: The algorithm appears polynomial when expressed in terms of certain parameters, but those parameters can themselves be exponential in the input size.

**Example - Clique Enumeration**:
- An algorithm might run in "O(n × number of cliques)" time
- This sounds polynomial if you treat "number of cliques" as a constant
- But a graph with n vertices can have up to 2^n cliques
- Therefore, the actual complexity is O(n × 2^n) = O(2^n), which is exponential

**Example - Vertex Clique Membership**:
- Similar to Hamelin (2011), an algorithm might be "bounded by the number of cliques each vertex belongs to"
- In a complete graph K_n, each vertex belongs to 2^(n-1) different cliques
- Runtime becomes exponential: O(n × 2^n)

#### 3. Incorrect Complexity Analysis

**The Problem**: Claiming polynomial time without rigorous proof of the time bound.

**Common Mistakes**:
- Counting iterations but not accounting for the cost of each iteration
- Assuming operations that are actually expensive can be done in constant time
- Using amortized or average-case analysis instead of worst-case
- Circular reasoning: "We can find cliques quickly, therefore we can find cliques quickly"

#### 4. Missing Correctness Proof

**The Problem**: Even if an algorithm runs in polynomial time, it must also be proven CORRECT (i.e., it always finds the maximum clique).

**Why This Matters**:
- A fast but incorrect algorithm doesn't solve the problem
- Many heuristics (like greedy algorithms) run quickly but don't guarantee optimal solutions
- The paper must prove: ∀G (algorithm(G) returns correct maximum clique)

### Typical Pattern of These Failures

Based on similar attempts in the literature (Hamelin 2011, Dhami et al. 2014), clique-based P = NP proofs typically follow this pattern:

1. ✅ Correctly identify that clique is NP-complete
2. ✅ Correctly note that a polynomial algorithm for clique would prove P = NP
3. ❌ Propose an algorithm with insufficient analysis
4. ❌ Fail to prove the algorithm works on ALL instances
5. ❌ Fail to prove the algorithm runs in polynomial time in the worst case
6. ❌ Fail to address why the algorithm overcomes known barriers

## Why This Approach Is Challenging

The clique problem has been extensively studied for over 50 years. If a simple polynomial-time algorithm existed, it would likely have been discovered. Several facts make polynomial-time clique algorithms unlikely:

### 1. Hardness Results

- **Inapproximability**: Unless P = NP, the maximum clique problem cannot be approximated within a factor of n^(1-ε) for any ε > 0 (Håstad, 1999)
- **Parameterized Complexity**: Clique is W[1]-hard, suggesting no f(k)·n^O(1) algorithm exists (where k is clique size)
- **Fixed-Parameter Intractability**: Finding a k-clique is believed to require n^Ω(k) time

### 2. Exponential Nature

- An n-vertex graph can have up to 2^n cliques
- The number of maximum cliques can be exponential
- Many natural approaches must examine exponentially many candidates

### 3. Lower Bounds (Conditional)

Under plausible complexity assumptions:
- Strong Exponential Time Hypothesis (SETH) implies no algorithm faster than n^((1-o(1))k) for finding k-cliques
- 3-SUM hardness implies certain approaches require superlinear time

## Broader Context

### Similar Attempts and Refutations

Several other researchers have claimed polynomial-time clique algorithms:

1. **Hamelin (2011)** - arXiv:1110.5355
   - **Error**: Runtime bounded by clique membership, which can be exponential
   - **Lesson**: Parameter bounds must be proven polynomial

2. **Dhami et al. (2014)** - arXiv:1403.1178 (withdrawn)
   - **Error**: Algorithm fails on large instances (admitted by authors)
   - **Refutation**: Cardenas et al. (2015), arXiv:1504.06890
   - **Lesson**: Algorithms must work on ALL instances, not just small or special cases

3. **LaPlante (2014)**
   - **Error**: Similar flaws to Dhami et al.
   - **Refutation**: Cardenas et al. (2015), arXiv:1504.06890
   - **Lesson**: Independent verification is essential

### The Community Response

Papers claiming P = NP typically receive scrutiny from the complexity theory community:
- Most are quickly identified as flawed
- Common errors are well-documented
- Woeginger's list (where this attempt appears) tracks these attempts
- Serious claims are published in peer-reviewed journals and withstand scrutiny

The fact that Akbari's paper appeared in WASET proceedings (not a traditional peer-reviewed venue) and the updated version appeared at a conference (rather than a journal) suggests limited peer review.

## Formalization Goals

In this directory, we formalize:

1. **The Clique Problem**: Formal definition in Lean, Coq, and Isabelle
2. **NP-Completeness**: What it means for clique to be NP-complete
3. **The Claim**: If clique ∈ P, then P = NP (this is correct)
4. **The Gap**: What would need to be proven for the claim to hold
5. **Common Failure Modes**: How polynomial-time claims typically fail

The formalization demonstrates:
- The logical structure of clique-based P = NP attempts
- The proof obligations that must be met
- Why meeting these obligations is non-trivial
- The distinction between "works sometimes" and "works always"

## Key Lessons

### 1. Universal Quantification Matters

**Requirement**: ∀ instances I, algorithm(I) is correct AND runs in polynomial time
**Insufficient**: ∃ instances I₁, I₂, ... where algorithm works well

### 2. Worst-Case vs. Average-Case

- P and NP are defined by **worst-case** polynomial time
- An algorithm that works "usually" or "on average" doesn't suffice
- The hard instances are specifically designed to be difficult

### 3. Hidden Complexity

- Complexity can hide in:
  - The number of iterations (exponential loops disguised as "bounded")
  - The cost per iteration (expensive operations counted as "constant time")
  - Data structure operations (claiming O(1) for operations that are actually O(n))
  - Parameter values (parameters that seem small but can be exponential)

### 4. Burden of Proof

When claiming P = NP:
- ✅ Required: Rigorous proof of correctness for ALL instances
- ✅ Required: Rigorous proof of polynomial time bound
- ✅ Required: Addressing known barriers and impossibility results
- ❌ Insufficient: Working examples on small inputs
- ❌ Insufficient: Intuitive explanations without formal proof
- ❌ Insufficient: Experimental results showing good average-case performance

### 5. Extraordinary Claims Require Extraordinary Evidence

- P vs NP is a Clay Millennium Prize problem with a $1M prize
- Thousands of researchers have worked on this problem
- Any claimed solution must explain why it succeeds where others failed
- Independent verification and peer review are essential

## References

### Primary Sources

- **Original Paper**: Akbari, Z.O. (2008). "A Deterministic Polynomial-time Algorithm for the Clique Problem and the Equality of P and NP Complexity Classes." Proceedings of World Academy of Science, Engineering and Technology, Volume 35.

- **Updated Version** (2013): Presented at IEEE/ACIS 12th International Conference on Computer and Information Science, titled "A polynomial-time algorithm for the maximum clique problem."

### Woeginger's List

- **Entry #49**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Comprehensive list of P vs NP proof attempts
  - Maintained by Gerhard Woeginger (until his passing in 2022)
  - Now maintained by the community

### Background on the Clique Problem

- **Karp, R.M.** (1972). "Reducibility Among Combinatorial Problems." *Complexity of Computer Computations*, pp. 85-103.
  - Original proof that clique is NP-complete

- **Garey, M.R., Johnson, D.S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.* W.H. Freeman.
  - Comprehensive reference on NP-completeness

### Hardness and Inapproximability

- **Håstad, J.** (1999). "Clique is hard to approximate within n^(1-ε)." *Acta Mathematica*, 182(1): 105-142.
  - Proves strong inapproximability results for clique

- **Zuckerman, D.** (2006). "Linear degree extractors and the inapproximability of max clique and chromatic number." *Theory of Computing*, 3(1): 103-128.

### Similar Attempts and Refutations

- **Hamelin, J.I.A.** (2011). "Is it possible to find the maximum clique in general graphs?" arXiv:1110.5355

- **Tamta, P., Pande, B.P., Dhami, H.S.** (2014). "A Polynomial Time Solution to the Clique Problem." arXiv:1403.1178 [Withdrawn]

- **Cardenas, H.A., et al.** (2015). "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890

### Complexity Theory Fundamentals

- **Cook, S.A.** (1971). "The complexity of theorem-proving procedures." *Proceedings of STOC*.
  - Introduced NP-completeness

- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach.* Cambridge University Press.
  - Modern textbook covering P, NP, and related topics

- **Sipser, M.** (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.
  - Accessible introduction to complexity theory

### The P vs NP Problem

- **Clay Mathematics Institute**: [P vs NP Official Problem Description](https://www.claymath.org/millennium/p-vs-np/)
  - Official problem statement for the Millennium Prize

## See Also

- [Dhami et al. 2014 Attempt](../dhami-2014-peqnp/) - Similar clique-based approach (withdrawn)
- [Hamelin 2011 Attempt](../hamelin-2011-peqnp/) - Clique algorithm with exponential hidden complexity
- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Repository README](../../../README.md) - Overview of the P vs NP problem

## Formalization Structure

```
proofs/attempts/zohreh-akbari-2008-peqnp/
├── README.md                    (this file)
├── coq/
│   └── AkbariAttempt.v         (Coq formalization)
├── lean/
│   └── AkbariAttempt.lean      (Lean 4 formalization)
└── isabelle/
    └── AkbariAttempt.thy       (Isabelle/HOL formalization)
```

## Status

- ✅ Documentation: Complete
- ✅ Lean formalization: Complete
- ✅ Coq formalization: Complete
- ✅ Isabelle formalization: Complete

---

**Note**: This formalization is for educational purposes to understand common pitfalls in P vs NP proof attempts. The goal is to build intuition about the problem, formalize the requirements for a valid proof, and understand why certain approaches fail.
