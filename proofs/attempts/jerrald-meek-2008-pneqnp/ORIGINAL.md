# Analysis of the postulates produced by Karp's Theorem

**Author**: Jerrald Meek
**Year**: 2008
**Source**: arXiv:0808.3222v5 [cs.CC] 3 Sep 2008
**URL**: https://arxiv.org/abs/0808.3222

## Abstract

This is the final article in a series of four articles. Richard Karp has proven that a deterministic polynomial time solution to K-SAT will result in a deterministic polynomial time solution to all NP-Complete problems. However, it is demonstrated that a deterministic polynomial time solution to any NP-Complete problem does not necessarily produce a deterministic polynomial time solution to all NP-Complete problems.

**Categories and Subject Descriptors**: F.2.0 [Analysis of Algorithms and Problem Complexity]: General
**General Terms**: Algorithms, Theory
**Additional Key Words and Phrases**: P vs NP, NP-complete

## 1. INTRODUCTION

The present author has previously shown that a NP-complete problem is solvable in deterministic polynomial time by a search algorithm if and only if a polynomial search partition can be found in polynomial time.

Additionally, it has been shown that some instances of the 0-1-Knapsack problem do not have a deterministic polynomial time solution, unless the SAT problem has a deterministic polynomial time solution.

This is the final article in a series of four, wherein the purpose will be to finally determine that the SAT problem has no deterministic polynomial time solution. It will then become clear that the 0-1-Knapsack problem, and any similar NP-complete problem which depends on SAT for a deterministic polynomial time solution, cannot be solved in deterministic polynomial time.

## 2. PRELIMINARIES

Previously the author has proven the following theorems, which will be assumed true in this article.

### 2.1. P = NP Optimization Theorem
(Theorem 4.4 from "P is a proper subset of NP" [Meek Article 1 2008])

The only deterministic optimization of a NP-complete problem that could prove P = NP would be one that can always solve a NP-complete problem by examining no more than a polynomial number of input sets for that problem.

### 2.2. P = NP Partition Theorem
(Theorem 5.1 from "P is a proper subset of NP" [Meek Article 1 2008])

The only deterministic search optimization of a NP-complete problem that could prove P = NP would be one that can always find a representative polynomial search partition by examining no more than a polynomial number of input sets from the set of all possible input sets.

### 2.3. Knapsack Random Set Theorem
(Theorem 5.1 from "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem" [Meek Article 2 2008])

Deterministic Turing Machines cannot exploit a random relation between the elements of S to produce a polynomial time solution to the Knapsack problem.

### 2.4. Knapsack Composition Theorem
(Theorem 6.1 from "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem" [Meek Article 2 2008])

Compositions of M cannot be relied upon to always produce a deterministic polynomial time solution to the 0-1-Knapsack problem.

### 2.5. Knapsack M Quality Reduction Theorem
(Theorem 6.2 from "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem" [Meek Article 2 2008])

Any quality of M that could be used to find a composition of M within S would be equivalent to finding all compositions of M.

### 2.6. Knapsack Set Quality Theorem
(Theorem 7.1 from "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem" [Meek Article 2 2008])

Using any quality of the elements of S to solve the 0-1-Knapsack problem will be no less complex than the standard means of solving the 0-1-Knapsack problem.

### 0-1-Knapsack Problem Definition

The definition of the 0-1-Knapsack problem used in this article is based on that used by Horowitz and Sahni [Horowitz and Sahni 1974]:

1. Let S be a set of real numbers with no two identical elements.
2. Let r be the number of elements in S.
3. Let δ be a set with r elements such that δᵢ ∈ {0, 1} ← 1 ≤ i ≤ r
4. Let M be a real number.

Then: Σᵢ₌₁ʳ δᵢSᵢ = M

Find a variation of δ that causes the expression to evaluate true.

---

**Note**: This is an automated conversion from the original PDF. For the complete paper with proper formatting, mathematical notation, and all sections, please refer to ORIGINAL.pdf or the arXiv source at https://arxiv.org/abs/0808.3222.

The paper continues with sections on:
- K-SAT to Knapsack Conversion
- K-SAT Input Relation
- No "Magical Solution"
- Conclusions
- References

**Full paper available**: See `ORIGINAL.pdf` in this directory or access online at https://arxiv.org/pdf/0808.3222.pdf
