# Alan Feinstein (2005) - P≠NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #20](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 20 (from Woeginger's list)
- **Author**: Craig Alan Feinstein
- **Year**: 2005 (first version), 2006 (published version)
- **Claim**: P ≠ NP
- **Paper Title**: "Complexity Theory for Simpletons" / "Complexity Science for Simpletons"
- **Publication**: arXiv:cs/0507008, also in *Progress in Physics*, July 2006
- **Source**: [arXiv:cs/0507008v7](https://arxiv.org/abs/cs/0507008)

---

## Summary

Craig Alan Feinstein's 2005 paper "Complexity Science for Simpletons" claims to prove that P ≠ NP by arguing that the Meet-in-the-Middle algorithm for SUBSET-SUM is optimal in a specific computational model he introduces, called the "Mabel-Mildred-Feinstein model of computation."

The paper uses an anthropomorphic approach, imagining two human computers named Mabel and Mildred who have different efficiency profiles for sorting and comparing operations. The author then attempts to use mathematical induction to prove that the Meet-in-the-Middle algorithm (running in O(2^(n/2)) time) is the fastest possible algorithm for SUBSET-SUM, concluding that since this is exponential time, SUBSET-SUM is not in P, and therefore P ≠ NP.

---

## The Main Argument

### The SUBSET-SUM Problem

Given:
- A set A = {a₁, ..., aₙ} of n integers
- A target integer b

Question: Does there exist a subset of A whose elements sum to b?

### The Meet-in-the-Middle Algorithm

1. Partition A into two subsets: A⁺ = {a₁, ..., a⌈n/2⌉} and A⁻ = {a⌈n/2⌉+1, ..., aₙ}
2. Compute S⁺ and S⁻ (the sets of all subset-sums of A⁺ and A⁻)
3. Sort S⁺ and b - S⁻ in ascending order
4. Compare elements from the sorted lists to find a match

This algorithm runs in O(2^(n/2)) time.

### The "Mabel-Mildred-Feinstein" Model

Feinstein introduces two hypothetical human computers:
- **Mabel**: Efficient at sorting (15 seconds for 10 integers), slow at comparing (20 seconds for 10 pairs)
- **Mildred**: Slow at sorting (20 seconds for 10 integers), efficient at comparing (15 seconds for 10 pairs)

The argument claims:
1. For Mabel, the Meet-in-the-Middle algorithm is optimal (base case n=4)
2. By induction, this remains true for all larger n
3. Since asymptotic running time is machine-independent up to polynomial factors, the Meet-in-the-Middle algorithm is optimal on all computers
4. Since O(2^(n/2)) is exponential, SUBSET-SUM ∉ P
5. Since SUBSET-SUM ∈ NP, therefore P ≠ NP

---

## The Error

The proof contains several fundamental flaws:

### 1. **Invalid Induction Step**

The inductive argument (pages 2-3) claims to prove that Meet-in-the-Middle is optimal for Mabel by showing:
- It solves each subproblem optimally
- It shares information between subproblems when possible

However, this does NOT prove optimality. The argument shows that Meet-in-the-Middle is efficient *among divide-and-conquer algorithms*, but it does not prove that divide-and-conquer is the optimal strategy.

**Counter-example structure**: The proof would equally "prove" that no polynomial-time algorithm exists for problems that DO have polynomial-time algorithms but also have exponential-time divide-and-conquer solutions.

### 2. **Confusion Between Algorithm Families**

The proof assumes that because Meet-in-the-Middle is optimal within a specific class of algorithms (those that partition the problem), it must be optimal among ALL algorithms. This is a category error.

**Analogy**: Proving that binary search is the fastest comparison-based sorting algorithm doesn't prove that comparison-based sorting is optimal (because radix sort exists and uses a different approach).

### 3. **The Machine Independence Argument is Misapplied**

The claim that "asymptotic running time does not differ by more than a polynomial factor when run on different types of computers" is true for a fixed algorithm, but Feinstein uses this to transfer optimality claims between machines, which is invalid.

**The flaw**:
- TRUE: If algorithm A runs in time T(n) on machine M₁, it runs in time O(T(n)) on machine M₂
- FALSE: If A is optimal on M₁, then A is optimal on M₂

Different computational models can have different optimal algorithms.

### 4. **Circular Reasoning About Lower Bounds**

The statement "it is impossible for such an algorithm to exist" (page 2, regarding faster algorithms) is asserted without proof. The paper assumes what it sets out to prove.

### 5. **Misunderstanding of Complexity Theory**

The paper conflates:
- **Worst-case complexity** (what P vs NP is about)
- **Optimality within a specific algorithmic paradigm** (what the induction proves, at best)

Even if Meet-in-the-Middle were optimal among all divide-and-conquer algorithms, this says nothing about whether a completely different algorithmic approach might work in polynomial time.

### 6. **Known Polynomial-Time Special Cases**

SUBSET-SUM has pseudo-polynomial time algorithms (dynamic programming in O(n·b) time where b is the target). This doesn't contradict NP-completeness (because b can be exponential in the input size), but it shows that the blanket claim "no algorithm faster than 2^(n/2)" is incorrect when considering the full structure of the problem.

---

## The Critical Gap

The proof attempts to show:

> "The Meet-in-the-Middle algorithm is optimal for Mabel (by induction) → Meet-in-the-Middle is optimal for all computers (by machine independence) → SUBSET-SUM requires exponential time → P ≠ NP"

The gap occurs at the first arrow: the induction proves at most that Meet-in-the-Middle is optimal *within a restricted class of algorithms*. The conclusion that no polynomial-time algorithm exists is unjustified.

This is analogous to proving that the fastest way to walk from New York to Los Angeles is to walk in a straight line, then concluding that no one can travel from New York to Los Angeles in less than walking time (ignoring planes, cars, etc.).

---

## Additional Issues

### The Collatz and Riemann Hypothesis Arguments

The paper also claims to prove that:
1. The Collatz 3n+1 Conjecture is unprovable
2. The Riemann Hypothesis is unprovable

These arguments are based on Kolmogorov complexity and computational irreducibility, but they contain similar logical flaws:

- **Collatz argument**: Claims that any proof must specify a "random" parity vector, but this assumes a specific proof structure (direct computation) and ignores the possibility of indirect proofs
- **Riemann argument**: Claims infinite time is needed to verify all zeros, but this assumes a specific verification method

### Reception

This paper has not been accepted by the complexity theory community. It appeared in *Progress in Physics*, which is not a peer-reviewed computer science or mathematics journal of record.

---

## Formalization Goals

The formal proof attempts in this directory aim to:

1. **Formalize the SUBSET-SUM problem** and the Meet-in-the-Middle algorithm
2. **Formalize the inductive argument** to understand exactly what it proves
3. **Identify the gap** where the proof claims more than it demonstrates
4. **Demonstrate the error** by showing that the reasoning pattern would prove false statements

By formalizing the argument, we make explicit the hidden assumptions and invalid logical steps.

---

## Files in This Directory

- **coq/**: Coq formalization of Feinstein's argument and the error
- **lean/**: Lean formalization of Feinstein's argument and the error
- **isabelle/**: Isabelle/HOL formalization of Feinstein's argument and the error
- **README.md**: This file

---

## References

1. Feinstein, C. A. (2005). "Complexity Science for Simpletons". arXiv:cs/0507008
2. Horowitz, E., & Sahni, S. (1974). "Computing Partitions with Applications to the Knapsack Problem". *Journal of the ACM*, 21(2), 277-292.
3. Woeginger, G. J. (2003). "Exact Algorithms for NP-Hard Problems: A Survey". *Lecture Notes in Computer Science*, 2570, 185-207.
4. Woeginger, G. J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

---

## Status

- ✅ Paper analyzed and error identified
- 🚧 Coq formalization in progress
- 🚧 Lean formalization in progress
- 🚧 Isabelle formalization in progress

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #108](https://github.com/konard/p-vs-np/issues/108) | [PR #390](https://github.com/konard/p-vs-np/pull/390)
