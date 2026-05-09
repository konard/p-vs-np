# Original Paper: On the existence of polynomial-time algorithms to the subset sum problem

**Author:** Jorma Jormakka  
**Year:** 2008 (submitted September 28, 2008; revised multiple times, final version November 20, 2020)  
**arXiv ID:** [arXiv:0809.4935](https://arxiv.org/abs/0809.4935)  
**Subject Classification:** General Mathematics (math.GM)  
**Woeginger's List:** Entry #47

---

## Abstract

This paper proves that there does not exist a polynomial-time algorithm to the subset sum problem. As this problem is in NP, the result implies that the class P of problems admitting polynomial-time algorithms does not equal the class NP of problems admitting nondeterministic polynomial-time algorithms.

**Key words:** computational complexity, polynomial-time, algorithm, knapsack problem.

---

## 1. Introduction

### Problem Definition

**Definition 1.** A knapsack is a pair of the form (j, (d₁, . . . , dₙ)) where j, n ∈ ℕ, j, n > 0 and dₖ ∈ ℕ, dₖ > 0 for 1 ≤ k ≤ n.

The **knapsack problem** (also called **subset sum problem**) asks: given a knapsack (j, (d₁, . . . , dₙ)), determine if there exist binary numbers cₖ ∈ {0, 1}, 1 ≤ k ≤ n, such that:

```
j = Σ(k=1 to n) cₖ·dₖ
```

### Polynomial-Time Definition

Let B, α ∈ ℝ, B ≥ 1, α ≥ 0 be fixed numbers. An algorithm A is called a **polynomial-time algorithm** to the knapsack problem if there exist numbers C, β ∈ ℝ that depend on B and α but not on n such that:

For any sequence of knapsacks ((jₙ, (d₁,ₙ, . . . , dₙ,ₙ)))ₙ≥₁ satisfying:

```
log₂ jₙ < Bn^α  
log₂ dₖ,ₙ < Bn^α  (for 1 ≤ k ≤ n, n ≥ 1)
```

the number Nₙ of elementary operations that algorithm A needs to produce an answer (yes or no) satisfies **Nₙ < Cn^β** for all n ≥ 1.

### Necessity of Upper Bounds

The definition includes upper bounds on jₙ and each dₖ,ₙ for two crucial reasons:

**(i) Binary representation growth:** If log₂ jₙ grows faster than any polynomial as a function of n, then the length of jₙ in binary representation also grows super-polynomially. Any operations requiring all bits of jₙ must require more than a polynomial number of elementary operations.

**(ii) Trivial polynomial solutions exist without bounds:** If jₙ has an upper bound independent of n, then a polynomial-time algorithm exists (see Lemma A2 in the Annex). The algorithm calculates an exponentially growing number of combinations in the same polynomial time.

Therefore, jₙ must grow polynomially with n to have a meaningful NP-complete knapsack problem.

---

## 2. The Main Inequality: (2.6) Means Non-Polynomial Time

### Key Insight

The paper's strategy is:
1. **Cannot use fixed problem sequence:** It's impossible to select a fixed sequence of specific subset sum problems and show no algorithm can solve this sequence in polynomial time (because we could create an algorithm specifically optimized for that sequence).
2. **Must use adversarial construction:** Instead, first select ANY algorithm, then pose it a sequence of problems that are particularly hard for THAT specific algorithm.

### Definition 2: The Computation Time Function f(n)

The paper defines f(n) as describing the "worst in the median" computation time for any selected algorithm.

**Construction:**
- For convenience, let n = 2^(i+2) for some i > 0
- Let h(d₁,ₙ, . . . , dₙ,ₙ, jₙ) be the computation time for deciding if knapsack (jₙ, (d₁,ₙ, . . . , dₙ,ₙ)) has a solution
- Define C = 2^(n/2 + 1)
- Let jₙ range over numbers jₙ ∈ {C + 1, . . . , 2^(n+1) - 1} where:
  - jₙ,ₗ = jₙ - C > 2^(n/4 + 2)  (jₙ,ₗ are the lower half bits of jₙ)
  - There is NO solution to the knapsack (jₙ, (d₁,ₙ, . . . , dₙ,ₙ))
  - Values of jₙ are computed separately (no reuse of partial results)

Define the **median computation time**:
```
Medianⱼₙ h(d₁,ₙ, . . . , dₙ,ₙ, jₙ)
```

Let (d₁,ₙ, . . . , dₙ,ₙ) range over all knapsack sequences with:
```
⌈log₂ Σ(k=1 to n) dₖ,ₙ⌉ = n   and   dₖ,ₙ ≤ 2^(n/(n-1))
```

The **worst in the median tuple** for n is an n-tuple (d₁,ₙ, . . . , dₙ,ₙ) that maximizes the median computation time.

Define:
```
f(n) = max(d₁,ₙ,...,dₙ,ₙ) Medianⱼₙ h(d₁,ₙ, . . . , dₙ,ₙ, jₙ)
```

**Why use median instead of worst case?** The median is used because the paper needs n/2 almost-as-long computations. Using worst case, a single very slow computation could dominate. With median and large n, the distribution of computation times becomes approximately normal (by law of large numbers), so many values give near-median time.

**Why only unsuccessful cases?** Including only unsuccessful cases means more complicated knapsack problems (more cases to check) give longer computation times.

### Lemma 1: The Recurrence Implies Super-Polynomial Growth

**Statement:** Let m be fixed and n be a power of m. If f(n) satisfies:
```
(n/m)·f(n/m) < f(n)
```
then f(n) does not grow polynomially with n.

**Proof sketch:**
1. Iterating gives: (n/m²)·f(n/m²) < f(n)
2. Iterating up to k yields: m^(Σᵢ₌₁ᵏ i)·f(n/m^k) < f(n)
3. Setting k = ln n / ln m (so 1 = n/m^k) gives:
   ```
   n^(ln n / (2 ln m))·n^(-1/2)·f(1) < f(n)
   ```
4. For any fixed m, this shows f(n) is not bounded by any polynomial.

### Theorem 1: Main Result

**Statement:** Let n ≥ 8 be a power of 2. There exists a sequence (d₁,ₙ, . . . , dₙ,ₙ) and subsets K₁, K₂, K₃ of the jₙ values in the median calculation such that:

```
n/2 · f(n/2) < f(n)        (inequality 2.6)
```

This means f(n) grows super-polynomially, so no polynomial-time algorithm exists for the subset sum problem.

---

## 3. Proof Strategy

The proof constructs three types of adversarial knapsack instances K₁, K₂, K₃ that force the algorithm to solve approximately n/2 subproblems of size n/2:

### Construction of Hard Instances

**K₁ instances:** Problems where the algorithm must check the lower n/2 positions
- Forces algorithm to solve subproblems on lower half bits
- Takes time ≈ f(n/2)

**K₂ instances:** Problems where the algorithm must check the upper n/2 positions  
- Forces algorithm to solve subproblems on upper half bits
- Takes time ≈ f(n/2)

**K₃ instances:** Mixed problems requiring both halves
- Forces algorithm to combine results from both halves
- Takes time ≈ f(n/2)

**Key claim:** For ANY algorithm, at least one-third of the median-time instances fall into one of {K₁, K₂, K₃}, and solving these requires time n/2 · f(n/2), establishing the recurrence relation (2.6).

---

## 4. Conclusion

The paper concludes that:
- For the subset sum problem, there exists no polynomial-time algorithm
- Since subset sum ∈ NP, this proves **P ≠ NP**

---

## Critical Mathematical Objects

1. **f(n)**: The "worst in the median" computation time function
2. **Recurrence (2.6)**: n/2 · f(n/2) < f(n)
3. **Adversarial instances K₁, K₂, K₃**: Problem instances tailored to each algorithm
4. **Median over unsuccessful cases**: Statistical measure avoiding single outliers
