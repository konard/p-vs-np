# Original Paper: Towards P = NP via k-SAT: A k-SAT Algorithm Using Linear Algebra on Finite Fields

**Author:** Matt Groff
**Year:** 2011 (submitted June 3, 2011; revised October 1, 2011)
**arXiv ID:** [1106.0683v2](https://arxiv.org/abs/1106.0683)
**Subject Classification:** Data Structures and Algorithms (cs.DS); Computational Complexity (cs.CC)
**Woeginger's List:** Entry #75

---

## Abstract

The problem of P vs. NP is very serious, and solutions to the problem can help save lives. This article is an attempt at solving the problem using a computer algorithm. It is presented in a fashion that will hopefully allow for easy understanding for many people and scientists from many diverse fields.

In technical terms, a novel method for solving k-SAT is explained. This method is primarily based on linear algebra and finite fields. Evidence is given that this method may require roughly O(n^3) time and space for deterministic models. More specifically the algorithm runs in time O(P · V(n + V)^2) with mistaking satisfiable Boolean expressions as unsatisfiable with an approximate probability 1/Θ(V(n + V)^2)^P, where n is the number of clauses and V is the number of variables. It's concluded that significant evidence exists that P=NP.

There is a forum devoted to this paper at http://482527.ForumRomanum.com. All are invited to correspond here and help with the analysis of the algorithm. Source code for the associated algorithm can be found at https://sourceforge.net/p/la3sat.

---

## 1 Introduction

There are many problems proposed to computer scientists that have been thought to be too difficult for computers to solve quickly. In fact, perhaps the most fundamental question in computer science is to find if certain types of problems, collectively known as the class NP, can be solved quickly by a computer. If so, a world of opportunities would open up, and many new problems that were supposed to be almost impossible to solve could be solved quickly. This paper attempts to provide a proof that they can be solved quickly, and also shows a way to do it.

The level of interest in this question is so great that in 2000, the Clay Mathematics Institute listed the 7 Millennium Prize Problems, and offered $1,000,000 for someone who could prove the relationship between P and NP [7], which would answer the question.

### 1.1 Turing Machines

To understand the classes P and NP, first consider the basic notion of a Turing machine, which is a scientific definition of a computer. A deterministic Turing machine (DTM) has a predetermined decision for every type of situation it encounters. A nondeterministic Turing machine (NTM), on the other hand, can have more than one action it can do for any given situation.

### 1.2 P and NP

Right around 1970, Leonid Levin (USSR) and Stephen Cook (US) independently arrived at the concept of NP-completeness [1].

- **P** is the class of all problems solvable by a DTM in polynomial time.
- **NP** is the class of all problems solvable by an NTM in polynomial time.
- **NP-complete** problems are in NP and at least as hard as all other problems in NP.

The fundamental question: Is P = NP?

### 1.3 SAT and k-SAT

SAT asks: given a Boolean formula, can the formula be satisfied (i.e., can all variables be assigned truth values making the formula true)? A certificate (a satisfying assignment) must be provided if the answer is yes.

k-SAT is a variant of SAT where the formula is in conjunctive normal form (CNF) with each clause containing exactly k variables. k-SAT (for k ≥ 3) is NP-complete.

Current best algorithms for 3-SAT run in exponential time (e.g., O(1.321^n) randomized, O(1.439^n) deterministic).

---

## 2 Data Structure(s)

One of the most fundamental components of the algorithm is the **clause polynomial**.

### Core Idea

For a system of V variables (x_0, x_1, ..., x_{V-1}), the complete truth table has 2^V rows. The clause polynomial for a single clause encodes, for each of the 2^V possible truth assignments, whether that assignment satisfies the clause.

The polynomial uses a single variable x, where the exponent of x encodes the truth assignment index, and the coefficient encodes satisfaction (1 = satisfied, 0 = not satisfied).

### Single-Variable Clause Polynomial

For variable x_m in a system of n+1 total variables:

```text
f(x_m) = (∏_{k=0}^{m-1} (1 + x^{2^k})) · x^{2^m} · (∏_{k=m+1}^{n} (1 + x^{2^k}))
```

This produces a polynomial where the coefficient of x^i is 1 if and only if truth assignment i has x_m = true.

**Example** (x_0 in system of x_0, x_1, x_2):
```text
f(x_0) = x^{2^0}(1 + x^{2^1})(1 + x^{2^2}) = x^1 + x^3 + x^5 + x^7
```
Coefficients: 0x^0 + 1x^1 + 0x^2 + 1x^3 + 0x^4 + 1x^5 + 0x^6 + 1x^7

(Assignments where x_0=1: indices 1, 3, 5, 7 in binary: 001, 011, 101, 111)

### 2.1 Constructing Clause Polynomials

For a clause x_{a_0} ∨ x_{a_1} ∨ · · · ∨ x_{a_n} (Algorithm in Figure 7):

```text
For each x_{a_i}:
  Calculate g(x_{a_i}) = (∏_{k=0}^{a_i-1} (1 + x^{2^k})) · x^{2^{a_i}}

Let Result = 0
For h = 0 to max_variable_index:
  If (h = a_i for some i):
    Result = Result + g(x_h)
  Else:
    Result = Result · (1 + x^{2^h})
Return Result
```

**Example**: f(x_0 ∨ x_1 ∨ x_2) = 0x^0 + 1x^1 + 1x^2 + 1x^3 + 1x^4 + 1x^5 + 1x^6 + 1x^7

(All assignments except the all-false assignment 000 satisfy x_0 ∨ x_1 ∨ x_2.)

### 2.2 Negation

Negation of a clause polynomial can be computed by swapping 1s and 0s in the coefficients, using the function of all ones:

```text
f(1) = ∏_{k=0}^{V-1} (1 + x^{2^k})
```

For negated variable x̄_m: compute f(1) - f(x_m) to flip all 0/1 coefficients.

---

## 3 The Algorithm

### 3.1 Manipulating Clause Polynomials

Before multiplication, the clause polynomials are modified:
- All coefficients equal to 1 are changed to a (a scalar in the finite field).
- All coefficients equal to 0 are changed to 1.

This is done via:
