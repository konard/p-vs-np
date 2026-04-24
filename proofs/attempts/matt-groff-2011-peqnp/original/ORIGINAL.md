# Original Paper: Towards P = NP via k-SAT: A k-SAT Algorithm Using Linear Algebra on Finite Fields

**Author:** Matt Groff
**Year:** 2011 (submitted June 3, 2011; revised October 1, 2011)
**arXiv ID:** [1106.0683v2](https://arxiv.org/abs/1106.0683)
**Subject Classification:** Data Structures and Algorithms (cs.DS); Computational Complexity (cs.CC)
**Woeginger's List:** Entry #75

---

## Abstract

The problem of P vs. NP is very serious, and solutions to the problem can help save lives. This article is an attempt at solving the problem using a computer algorithm. It is presented in a fashion that will hopefully allow for easy understanding for many people and scientists from many diverse fields.

In technical terms, a novel method for solving k-SAT is explained. This method is primarily based on linear algebra and finite fields. Evidence is given that this method may require roughly O(n³) time and space for deterministic models. More specifically the algorithm runs in time O(P · V(n + V)²) with mistaking satisfiable Boolean expressions as unsatisfiable with an approximate probability 1/Θ(V(n + V)²)^P, where n is the number of clauses and V is the number of variables. It's concluded that significant evidence exists that P=NP.

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

Current best algorithms for 3-SAT run in exponential time (e.g., O(1.321ⁿ) randomized, O(1.439ⁿ) deterministic).

---

## 2 Data Structure(s)

One of the most fundamental components of the algorithm is the **clause polynomial**.

### Core Idea

For a system of V variables (x₀, x₁, ..., x_{V-1}), the complete truth table has 2^V rows. The clause polynomial for a single clause encodes, for each of the 2^V possible truth assignments, whether that assignment satisfies the clause.

The polynomial uses a single variable x, where the exponent of x encodes the truth assignment index, and the coefficient encodes satisfaction (1 = satisfied, 0 = not satisfied).

### Single-Variable Clause Polynomial

For variable x_m in a system of n+1 total variables:

```
f(x_m) = (∏_{k=0}^{m-1} (1 + x^{2^k})) · x^{2^m} · (∏_{k=m+1}^{n} (1 + x^{2^k}))
```

This produces a polynomial where the coefficient of x^i is 1 if and only if truth assignment i has x_m = true.

**Example** (x₀ in system of x₀, x₁, x₂):
```
f(x₀) = x^{2⁰}(1 + x^{2¹})(1 + x^{2²}) = x¹ + x³ + x⁵ + x⁷
```
Coefficients: 0x⁰ + 1x¹ + 0x² + 1x³ + 0x⁴ + 1x⁵ + 0x⁶ + 1x⁷

(Assignments where x₀=1: indices 1, 3, 5, 7 in binary: 001, 011, 101, 111)

### 2.1 Constructing Clause Polynomials

For a clause x_{a₀} ∨ x_{a₁} ∨ · · · ∨ x_{aₙ} (Algorithm in Figure 7):

```
For each x_{aᵢ}:
  Calculate g(x_{aᵢ}) = (∏_{k=0}^{aᵢ-1} (1 + x^{2^k})) · x^{2^{aᵢ}}

Let Result = 0
For h = 0 to max_variable_index:
  If (h = aᵢ for some i):
    Result = Result + g(x_h)
  Else:
    Result = Result · (1 + x^{2^h})
Return Result
```

**Example**: f(x₀ ∨ x₁ ∨ x₂) = 0x⁰ + 1x¹ + 1x² + 1x³ + 1x⁴ + 1x⁵ + 1x⁶ + 1x⁷

(All assignments except the all-false assignment 000 satisfy x₀ ∨ x₁ ∨ x₂.)

### 2.2 Negation

Negation of a clause polynomial can be computed by swapping 1s and 0s in the coefficients, using the function of all ones:

```
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
```
h(x) = a · f(x) + (f(1) - f(x))
```
where f(1) = 1·x⁰ + 1·x¹ + ... + 1·x^{2^V-1} is the function of all ones.

For addition, the exponents of x are doubled: x^i → x^{2i}.

### 3.2 Multiplication

Multiplying two clause polynomials (in their modified form) produces a matrix product where:
- The diagonal entries (Hadamard product) represent satisfaction counts.
- The off-diagonal entries represent "interference" terms.

Key insight: Boolean conjunction (AND) and arithmetic multiplication agree on {0,1} values:
```
0·0 = 0 (False AND False = False)
0·1 = 0 (False AND True = False)
1·0 = 0 (True AND False = False)
1·1 = 1 (True AND True = True)
```

After modification with scalar a:
- The coefficient 1·1 (both clauses satisfied) → 1 · a = a
- The coefficient 1·0 (one clause satisfied) → 1
- The coefficient 0·0 (no clause satisfied) → 0

The three cases are distinguished by the resulting value (0, a, or a²).

### 3.3 Multiplication and Satisfaction

With modified coefficients {0 → 1, 1 → a}:
- 0 clauses satisfied: coefficient → 1·1 = 1 (under multiplication with complemented form)
- 1 clause satisfied: coefficient → 1·a or a·1 = a
- 2 clauses satisfied: coefficient → a·a = a²

The algorithm is interested in the case a² (both clauses satisfied).

### 3.4 Eliminating the Diagonal

Using two multiplication operations and one addition operation:

Choose constants a₀, a₁ (distinct field elements ≠ 0,1) and scalars c₀, c₁.
The three diagonal cases must satisfy:
```
c₀ + c₁ - d = 0         ...(3.3)
c₀a₀ + c₁a₁ - (d+1) = 0  ...(3.4)
c₀a₀² + c₁a₁² - (d+2) = 0 ...(3.5)
```
These equations can be solved to eliminate diagonal values, leaving only off-diagonal terms.

The off-diagonal terms are represented as unknowns b₀, b₁, b₂ (counts of 0, 1, and 2 clauses satisfied), yielding one equation:
```
4b₀ + 2b₁ + 0b₂ = some_value
```

### 3.5 Finite Field Arithmetic (Modular Arithmetic)

All calculations are performed modulo a prime p. This gives a finite field GF(p) with p elements.

The prime p is chosen to be greater than (2n)² (where n is the number of clauses). This bounds the probability of false results.

The second-order differences method: given the sequence c·1, c·a, c·a², the differences and second differences are computed to find matching pairs of equations that cancel the diagonal.

---

## 4 A Two Clause Walkthrough

Initial problem: (x₀) ∧ (x̄₀ ∨ x₁)

1. Choose p = 17 (prime, 17 > (2·2)² = 16).
2. Choose x = 3 (for polynomial evaluation).
3. Compute f(x₀) = (1 + x²)·x¹ = (1+9)·3 = 30 ≡ 13 (mod 17).
4. Compute f(x̄₀ ∨ x₁) ≡ 3 (mod 17) (by algorithm of Figure 10).
5. Choose a₀ = 2. Compute second-order differences for each choice of c₀.
6. Choose a₁ = 3 with c₁ = 1. Second-order difference = 4. Need 17-4=13 from first equation. Choose c₀ = 13.
7. Combine equations to get the off-diagonal linear system.
8. Solve the 2×2 system to get b₀ and b₁ (count of 0, 1 clause satisfied).
9. Compute b₂ = f(1) - b₀ - b₁ (count of 2 clauses satisfied).
10. If b₂ ≠ 0, the formula is satisfiable.

*(Section left incomplete in the original paper with "to be completed later...")*

---

## 5 Finishing The Two Clause Example

Key observation: The three unknowns b₀, b₁, b₂ are not independent — they sum to f(1) (the total number of truth assignments = 2^V). So the system reduces to 2 independent unknowns.

Two equations in two unknowns → solved by linear algebra (no division needed, just multiplication) in GF(p).

---

## 6 Algorithm Finish (Basics)

**Decision**: If the number of n-clause-satisfied assignments is nonzero, output SAT. Otherwise, output UNSAT with probability of error ≈ 1/Θ(V(n+V)²)^P.

**Certificate generation**: To find a satisfying assignment:
1. Run algorithm with x₁ = true. If satisfiable, continue.
2. Run algorithm with x₁ = true, x₂ = true. If satisfiable, continue.
3. ... and so on for each variable.
4. If fixing a variable to true makes the formula unsatisfiable, fix it to false instead.
5. Repeat until all V variables are assigned.

This runs the basic algorithm O(V) additional times.

---

## 7 The n Clause Algorithm

**Structure**: Use a binary tree of 2-clause algorithms.
- Each 2-clause algorithm takes 2 clauses as input and produces 1 output (the count of both-satisfied assignments).
- For n clauses, there are O(log n) levels.
- Total number of 2-clause algorithm calls: O((n+V)²) for setup, times O(V) for certificate.
- Total: **O(V · (n+V)²)** calls to the 2-clause algorithm.

**Semi-optimized Version**: The same prime p and setup values can be reused across iterations, so precomputation amortizes some cost.

---

## 8 Algorithm Complexity

Using P independent primes:
- Runtime: **O(P · V(n + V)²)**
- Error probability: **≈ 1/Θ(V(n+V)²)^P**

For large P, the error probability becomes negligible. The author claims this is polynomial in n and V, and thus would imply P = NP.

---

## 9 Conclusion

> "I hope that this project presents sufficient evidence that P=NP. I've written the last few pages rather hastily, but hope to improve things soon. I'm starting on writing the code for this project, so that everything can be put under better scrutiny."

---

## Appendix A: Proof of Clause Polynomial Construction

The appendix contains a formal proof that the clause polynomial construction algorithm (Figure 7) correctly produces polynomials whose coefficients encode satisfaction of each truth assignment. The proof uses mathematical induction on the number of variables.

**Key Formula (Equation B in paper)**:
```
f(1) = ∏_{k=0}^{V-1} (1 + x^{2^k})
```

This equals the polynomial with coefficient 1 for every monomial x^i for i = 0, 1, ..., 2^V - 1.

---

## References

- [1] Cook-Levin theorem: Cook, S.A. "The complexity of theorem-proving procedures." Proceedings, Third Annual ACM Symposium on the Theory of Computing, 1971.
- [6] Sipser, M. "The History and Status of the P versus NP Question." Proceedings of the 24th Annual ACM Symposium on Theory of Computing, 1992.
- [7] Devlin, K.J. "The Millennium Problems: The Seven Greatest Unsolved Mathematical Puzzles Of Our Time." 2002.
- [12] Wikipedia: Boolean satisfiability problem.
- [16] Iwama, K. et al. "Improved Randomized Algorithms for 3-SAT." ISAAC 2010.
- [20] Baker, T.P., Gill, J., Solovay, R. "Relativizations of the P =? NP Question." SIAM J. Computing, 1975.
