# How to solve kSAT in polynomial time

**Author:** Algirdas Antano Maknickas
**Year:** 2011 (published March 2011, revised March 2012)
**arXiv:** arXiv:1203.6020v2 [cs.CC]
**Source:** https://arxiv.org/abs/1203.6020

---

## Abstract

In this paper is shown that Satisfiability problem can be solved in polynomial time using multi-nary logic analytic formulas in modulo form. Also is proved that using such type of formulas k-SAT can be solved in polynomial time. The main result is that k-SAT can be solved in polynomial time by using multi-nary logic, and so P = NP.

---

## 1. Introduction

The most important and unsolved problem in computer science is the P vs NP problem. The P vs NP problem asks whether every problem whose solution can be quickly verified (technically, verified in polynomial time) can also be solved quickly (again in polynomial time). Formulated by Cook in 1971 [Cook 1971], this problem remains open. This paper proposes a polynomial-time algorithm for k-SAT using a novel formulation via multi-nary logic analytic formulas.

---

## 2. Multi-nary Logic Analytic Formulas

### 2.1 Basic Definitions

**Definition 1.** For integer n ≥ 2 and integer k, define:

```
gₙᵏ(a) = ⌊a⌋ + k (mod n)
```

where ⌊a⌋ denotes the floor function applied to a.

**LEMMA 1.** If n=2, function gₙᵏ(a) generates one-variable binary logic functions.

*Proof.* For n=2:
- g₂⁰(a) = ⌊a⌋ mod 2
- g₂¹(a) = (⌊a⌋ + 1) mod 2

When a ∈ {0,1}, g₂⁰(0) = 0, g₂⁰(1) = 1 (identity), and g₂¹(0) = 1, g₂¹(1) = 0 (negation). Thus these generate all one-variable Boolean functions. □

**LEMMA 2.** If n=2, function gₙᵏ(a*b) generates two-variable binary logic functions.

*Proof.* Consider the product a*b for Boolean values a,b ∈ {0,1}:
- a*b = 0 unless a=b=1
- g₂⁰(a*b) gives 0 for (0,0),(0,1),(1,0) and 1 for (1,1): this is AND
- g₂¹(a*b) gives 1 for (0,0),(0,1),(1,0) and 0 for (1,1): this is NAND

By composing such functions, all two-variable Boolean functions can be generated. □

**LEMMA 3.** If n>2, function gₙᵏ(a) generates one-variable multi-nary logic functions.

*Proof sketch.* For n-valued logic with values in {0,...,n-1}, gₙᵏ maps value v to (v+k) mod n, generating all cyclic shifts of the n-valued domain. □

**LEMMA 4.** If n>2, function gₙᵏ(a*b) generates two-variable multi-nary logic functions (analogous generalization of Lemma 2). □

### 2.2 Expressing Boolean Connectives

For n=2 and Boolean variables Xi ∈ {0,1}:

- **NOT**: ¬Xi = g₂¹(Xi) = (Xi + 1) mod 2
- **AND**: Xi ∧ Xj is related to the product Xi * Xj
- **OR**: Xi ∨ Xj = ¬(¬Xi ∧ ¬Xj) (De Morgan)

The paper introduces aggregation functions:

```
β₂(X₁, X₂, ..., Xₙ) = max over all pairs (Xi₋₁, Xi)
β₃(X₁, X₂, ..., Xₙ) = max over all triples (Xi₋₂, Xi₋₁, Xi)
βₖ(X₁, X₂, ..., Xₙ) = max over all k-tuples
```

---

## 3. Reduction of k-SAT to Linear Programming

### 3.1 2-SAT Case

**Theorem 1.** The 2-SAT problem for n variables and m clauses can be expressed as:

```
max β₂(X₁, X₂, ..., Xₙ)
```

subject to:

```
Xi₋₁ + Xi ≤ 2    for all relevant pairs
Xi ≥ 0            for all i
```

**Theorem 2.** The above LP can be solved in O(n^3.5) time.

*Proof.* Linear programming can be solved in polynomial time by interior point methods, specifically O(n^3.5) by Karmarkar's algorithm [Karmarkar 1984]. □

### 3.2 3-SAT Case

**Theorem 3.** The 3-SAT problem for n variables and m clauses can be expressed as:

```
max β₃(X₁, X₂, ..., Xₙ)
```

subject to:

```
Xi₋₂ + Xi₋₁ + Xi ≤ 3    for all relevant triples
Xi ≥ 0                    for all i
```

**Theorem 4.** The above LP for 3-SAT can be solved in O(n^3.5) time.

### 3.3 k-SAT Case

**Theorem 5.** The k-SAT problem for n variables and m clauses can be expressed as:

```
max βₖ(X₁, X₂, ..., Xₙ)
```

subject to:

```
∑ᵢ₌ⱼʲ⁺ᵏ⁻¹ Xᵢ ≤ k    for all relevant k-tuples
Xᵢ ≥ 0               for all i
```

**Theorem 6.** The above LP for k-SAT can be solved in O(n^3.5) time.

---

## 4. Recovering the Boolean Solution

After solving the LP, convert the real-valued solution back to Boolean values using:

```
X̃ᵢ = g₀²(Xᵢ) = ⌊Xᵢ⌋ (mod 2)    ∀i ∈ {1, 2, ..., n}
```

That is, a variable is TRUE if the floor of its LP value is even, FALSE if it is odd.

---

## 5. Main Result

**Main Theorem.** k-SAT can be solved in polynomial time O(n^3.5).

*Proof.*
1. Transform the k-SAT instance to an LP as described in Section 3.
2. Solve the LP in O(n^3.5) time using Karmarkar's algorithm.
3. Recover the Boolean solution using the floor-modulo function from Section 4.
4. Since k-SAT is NP-complete and can now be solved in polynomial time, P = NP. □

---

## 6. Conclusion

Every mathematical problem is solvable in polynomial time if there exists a full, appropriate and correct knowledge basis for it and the time to get each item of the knowledge basis is much less than the calculation time on these items. In particular, the approach shows k-SAT ∈ P, and therefore P = NP.

---

## References

- Cook, S. A. (1971). "The complexity of theorem proving procedures." Proceedings of the 3rd Annual ACM Symposium on Theory of Computing, 151–158.
- Karmarkar, N. (1984). "A new polynomial-time algorithm for linear programming." Combinatorica, 4(4), 373–395.
- Maknickas, A. A. (2010). "Finding of k in Fagin's R. Theorem 24." arXiv:1012.5804v1.
- Weiss, A. (2011). "A Polynomial Algorithm for 3-sat." (unpublished).
- Kardash, S. (2011). "Algorithmic complexity of pair cleaning method." arXiv:1108.0408v1.
- Groff, M. (2011). "Towards P = NP via k-SAT." arXiv:1106.0683v2.

---

*Note: This markdown is a faithful reconstruction of the paper's mathematical content from arXiv:1203.6020v2. The original PDF is available as [ORIGINAL.pdf](ORIGINAL.pdf).*
