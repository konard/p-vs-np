# The Complexity of 3SAT_N and the P versus NP Problem

**Author:** Ruijia Liao  
**arXiv:** 1101.2018v4 [cs.CC]  
**Submitted:** January 11, 2011; Last revised: November 11, 2013  
**Woeginger's List:** Entry #71

---

## Abstract

We introduce the NP-complete problem 3SAT_N and extend Tovey's results to a classification theorem for this problem. This theorem leads us to generalize the concept of truth assignments for SAT to aggressive truth assignments for 3SAT_N. We introduce the concept of a set compatible with the P versus NP problem, and prove that all aggressive truth assignments are pseudo-algorithms. We combine algorithm, pseudo-algorithm and diagonalization method to study the complexity of 3SAT_N and the P versus NP problem. The main result is P ≠ NP.

---

## 1. Introduction

In computational complexity theory, the Boolean satisfiability problem (SAT) is a decision problem, in which the instance is a Boolean expression written using only AND, OR, NOT, variables, and parentheses. The question is: given the expression, is there some assignment of true and false values to the variables that make the entire expression true? SAT is the first known NP-complete problem, proven by Stephen Cook in 1971 [6]. Independently in 1973, Leonid Levin showed that a variant of the tiling problem is NP-complete [9]. In 1972, Richard Karp proved that several other problems were also NP-complete [10]. In particular, the Boolean satisfiability problem remains NP-complete even if all expressions are written in conjunction normal form with 3 variables per clause (3-CNF), yielding the 3SAT problem.

We can define the kSAT problem in a similar way. Let (r,s)-SAT be the class of instances with exactly r distinct variables per clause and at most s occurrences per variable. In 1984 [13], Craig Tovey proved that every instance of (r,r)-SAT is satisfiable and (3,4)-SAT is NP-complete. Indeed, using these (3,s)-SAT for s = 1,...,4 and the results in [13], we can easily classify all instances in 3SAT by polynomial time in each instance's length.

In this paper, we use Tovey's idea in [13] to classify the NP-complete problem 3SAT_N. We prove that this classification takes polynomial time. With this classification theorem, we introduce the concept of aggressive truth assignment. We also introduce the concept of a set compatible with the P versus NP problem. Any element in a set that is compatible with the P versus NP problem is a pseudo-algorithm. We can prove that the set of all aggressive truth assignments is compatible with the P versus NP problem, and hence any aggressive truth assignment is a pseudo-algorithm. Using these pseudo-algorithms, we endow some set of algorithms with a metric and then introduce Cauchy sequences among them. The Cauchy sequences of algorithms in this paper are essentially the Cauchy sequences of pseudo-algorithms. Like the role of Cauchy sequences of rational numbers in real number theory, the Cauchy sequences of algorithms allow us to use pseudo-algorithms to approximate some algorithms. In 1874, Cantor [4] established that real numbers are uncountable. Sixteen years later, he proved his theorem again using diagonal argument [5]. Surprisingly, by analyzing computations of some pseudo-algorithms, we can use Cantor's diagonalization method to prove that there are uncountably many algorithms under some assumption. It contradicts the fact that there are only countably many algorithms (see e.g. [8]). Therefore, the assumption must be false.

In 1975, T.Baker, J.Gill, and R.Solovary [3] introduced the following relativized worlds: there exist oracles A and B, such that P^A ≠ NP^A and P^B = NP^B. They also pointed out that the relativizing method could not solve the P versus NP problem. In the early 1990's, A.Razborov and S.Rudich [11] defined a general class of proof techniques for circuit complexity lower bounds, called natural proofs. At the time all previously known circuit lower bounds were natural, and circuit complexity was considered a very promising approach for resolving P=NP. However, Razborov and Rudich showed that, if certain kinds of one-way functions exist, then no natural proof method can distinguish between P and NP. Although one-way functions have never been formally proven to exist, most mathematicians believe that they do. Thus it is unlikely that natural proofs alone can resolve P=NP.

In 1992, A.Shamir [12] used a new non-relativizing technique to prove IP = PSPACE. However, in 2008, S.Aaronson and A.Wigderson [1] showed that the main technical tool used in the IP = PSPACE proof, known as arithmetization, was also insufficient to resolve P=NP. In this paper, each pseudo-algorithm can be explicitly expressed by Algorithm 1 or Algorithm 2, and Algorithm 3; however, it is not an algorithm. It takes finite steps to partially evaluate any η ∈ 3SAT and, most importantly, it is different from any oracle and arithmetization. Since the new argument combines algorithm, pseudo-algorithm and diagonalization method, it circumvents relativization, natural proofs and algebrization.

In Section 2, we give some definitions and notations, we describe two similar algorithms and show that one is always more efficient than another. Using this result and the same argument, we prove in Section 8 that any element in some algorithm sequence is always more efficient than some polynomial time algorithm. We prove that 3SAT_N is an NP-complete problem in Section 3. We extend Tovey's results in [13] to a classification theorem in 3SAT_N and define another algorithm in Section 4. We generalize the concept of truth assignment to aggressive truth assignments in Section 5 based on the Classification Theorem. We define the composition of two or more aggressive truth assignments and investigate TA∞, a set of all aggressive truth assignments under this operation. We introduce the concept of distance between any two elements in TA∞ and endow it with a metric.

In Section 6, we extend this metric concept to <f>, a set of algorithms generated by algorithm f and aggressive truth assignments, in which we define Cauchy sequences. We give the definition of pseudo-algorithms. In Section 7, we discuss equivalence of algorithms and pseudo-algorithms and set up an equivalence relation in <f>. Any two elements in TA₁ are always equivalent. However, TA₂ has infinitely many equivalence classes. In Section 8, we introduce the concept of regular Cauchy sequence in <f>₂. It is critically important to be able to construct an algorithm f_ζ from {f_n}, an arbitrarily given regular Cauchy sequence. Such f_ζ is called the representation of {f_n}. We generalize the concept of equivalence relation from <f> to the set of all regular Cauchy sequences in <f>₂, and prove that any two regular Cauchy sequences in different equivalence classes have different representations and represent two different algorithms. For any regular Cauchy sequence {f_{a_n a_0}}, there exists a polynomial time algorithm f_{ã₀ã₀} which is less efficient than f_{a_n a_0} for n = 1,2,..., thus, its representation f_ζ is always a polynomial time algorithm. We show that the set of all aggressive truth assignments is a compatible set with the P versus NP problem in Section 9. Using the regular Cauchy sequences and diagonalization method, we prove that P ≠ NP in Section 10.

---

## 2. Preliminary

Let SAT(n)(x₁,...,xₙ) be the set of all expressions in SAT in which each element uses exactly n variables and their negations {x₁,...,xₙ,¬x₁,...,¬xₙ}. From the definition, SAT(n) ∩ SAT(n+1) = ∅ and ∪_{n≥3}^∞ SAT(n) ⊆ SAT. For r ≤ n and 1 ≤ s, let (r,s)-SAT(n) = (r,s)-SAT ∩ SAT(n). We can show that, for any η ∈ SAT, there exists a polynomial time algorithm in the length of η to find the integer n such that η is generated by variables and their negations {x_{i₁},...,x_{iₙ},¬x_{i₁},...,¬x_{iₙ}} where i₁ < ... < iₙ. Furthermore, there exists a linear time map φ_map, such that φ_map(x_{ik}) = xk, φ_map(¬x_{ik}) = ¬xk, for k = 1,...,n and η̃ = φ_map(η) ∈ SAT(n). Thus, if η ∈ (r,s)-SAT, then η̃ = φ_map(η) ∈ (r,s)-SAT(n) for some n. Obviously, η̃ is satisfiable if and only if η is satisfiable, and the numbers of clauses of η̃ and η are the same.

The map x*_i from {x_j, ¬x_j} to {true, false, undef} is defined as x*_i(x_i) = true, x*_i(¬x_i) = false, x*_i(x_j) = undef and x*_i(¬x_j) = undef if i ≠ j. The map ¬x*_i is defined similarly. An atomic truth assignment e_i is defined as e_i = x*_i or e_i = ¬x*_i.

Let η = (y_{1,1} ∨ ... ∨ y_{1,j₁}) ∧ (y_{2,1} ∨ ... ∨ y_{2,j₂}) ∧ ... ∧ (y_{m,1} ∨ ... ∨ y_{m,jₘ}) ∈ SAT(n), where y_{i,j} = x_k or ¬x_k for some k. A truth assignment e₁e₂...eₙ is defined as:

e₁e₂...eₙ(η) = (e_{1,1}(y_{1,1}) ∨ ... ∨ e_{1,j₁}(y_{1,j₁})) ∧ (e_{2,1}(y_{2,1}) ∨ ... ∨ e_{2,j₂}(y_{2,j₂})) ∧ ... ∧ (e_{m,1}(y_{m,1}) ∨ ... ∨ e_{m,jₘ}(y_{m,jₘ})) ∈ {true, false}.

**Algorithm 1.**
```
for k = 1,2,...,m
  evaluate clause (y_{k,1} ∨ ... ∨ y_{k,j_k}) as follows:
    for l = 1,2,...,j_k
      for p = 1,2,...,n
        if e_p(y_{k,l}) = undef, continue to inner loop
        if e_p(y_{k,l}) = false and l < j_k, continue to middle loop
        if e_p(y_{k,l}) = false and l = j_k, return false
        if e_p(y_{k,l}) = true
          if k < m, continue to outer loop
          if k = m, return true
```

This is a polynomial time algorithm.

**Algorithm 2.** (Similar to Algorithm 1 but counts unsatisfied clauses — always takes more steps.)

```
set c_g = 0
for k = 1,2,...,m
  c_l = 0
  for l = 1,2,...,j_k
    for p = 1,2,...,n
      if e_p(y_{k,l}) = undef, continue
      if e_p(y_{k,l}) = false and l < j_k, continue
      if e_p(y_{k,l}) = false and l = j_k
        if c_l = 0, increase c_g by 1
        if k < m, continue; if k = m, return c_g
      if e_p(y_{k,l}) = true, increase c_l by 1
        if l = j_k and k < m, continue
        if l = j_k and k = m, return c_g
```

Return value c_g = 0 if and only if η evaluates to true.

**Lemma 1.** For any two truth assignments and any η ∈ SAT(n), if s₁ and s₂ are the numbers of steps using Algorithm 1 and Algorithm 2 respectively, then s₁ < s₂.

For any integers m ≥ n ≥ 3, we can apply the truth assignment e₁e₂...eₘ to any instance of SAT(n). A **generalized truth assignment** e₁e₂...eₙ... is defined by finite information (it maps to a rational number in [0,1] via its binary encoding).

**Remark 1.** Define Φ(e₁e₂...eₖ...) = 0.φ(e₁)φ(e₂)...φ(eₖ)..., where φ(x*_i) = 1 and φ(¬x*_i) = 0. The finite information assumption means Φ maps any generalized truth assignment to a rational number in [0,1]. Thus there are only countably many generalized truth assignments.

---

## 3. An NP-complete Problem

Let η be an instance of kSAT. A clause y_{i₁} ∨ ... ∨ y_{ik} is called a **tautological clause** if it contains both x and ¬x for some variable x. A clause is called a **full clause** if it has k distinct variables. An expression is a **normal expression** if: (1) it has no tautological clause, (2) it has no repeated clause, and (3) each clause is full. Define:

kSAT_N = {η | η ∈ kSAT and η is a normal expression}

**Theorem 1.** 3SAT_N is NP-complete.

*Proof sketch.* 3SAT_N ∈ NP is clear. To show completeness, any η ∈ 3SAT can be reduced to η̃ ∈ 3SAT_N in polynomial time by:
1. Removing all tautological clauses;
2. Removing repeated clauses;
3. Removing repeated variables in clauses;
4. Replacing 1-literal and 2-literal clauses with equivalent 3-literal gadgets using auxiliary variables.

The gadget for forcing x = true uses nine clauses; the gadget for forcing x ∨ y uses five clauses. The complete reduction runs in polynomial time. □

For n ≥ 3, n ≥ k, n ≥ r and s ≥ 1, define:

- kSAT_N(n) = kSAT(n) ∩ kSAT_N
- SAT_N(n) = SAT(n) ∩ SAT_N
- (r,s)-SAT_N(n) = (r,s)-SAT(n) ∩ SAT_N(n)

---

## 4. A Classification Theorem

**Theorem 2 (Classification Theorem).** For every instance η of 3SAT_N, one of the following is true:
1. η ∈ (3,1)-SAT_N and η is satisfiable,
2. η ∈ (3,2)-SAT_N and η is satisfiable,
3. η ∈ (3,3)-SAT_N and η is satisfiable,
4. η ∈ (3,4)-SAT_N, or
5. η can be reduced to η̃ ∈ (3,4)-SAT_N in polynomial time.

Moreover, checking if η ∈ ∪_{s=1}^{3}(3,s)-SAT_N takes polynomial time.

*Proof.* Cases (1)-(3) follow from Tovey's theorem (every (r,r)-SAT instance is satisfiable) and extensions. Case (4)-(5) follow from Tovey's result that (3,4)-SAT is NP-complete and any (3,s)-SAT with s > 4 can be reduced to (3,4)-SAT in polynomial time.

The reduction can be improved: for any variable with more than 4 occurrences in η, split it into k copies with cyclic implication clauses, reducing occurrences to ≤ 4. This reduces m clauses to at most 31m clauses. □

**Corollary 1.** ∪_{s=1}^{4}(3,s)-SAT_N is NP-complete.

**Corollary 2.** ∪_{n≥3}^∞ 3SAT_N(n) is NP-complete.

**Algorithm 3.** (Checks if all variables have < 4 occurrences in η — polynomial time.)
```
for i = 1,2,...,n
  c = 0
  for j = 1,2,...,3(m+1)
    if e_i(y_{k_j}) = true or false, increase c by 1
    if c > 3, return false
  if i = n, return true
```

---

## 5. Aggressive Truth Assignments

An **aggressive truth assignment** e₁e₂...eₘ for η ∈ 3SAT_N(n) works as:
1. Evaluate η using Algorithm 1. If result is true, return true.
2. Check if η ∈ ∪_{s=1}^{3}(3,s)-SAT_N(n) using Algorithm 3. If so, return true; otherwise return false.

A **less efficient aggressive truth assignment** uses Algorithm 2 in step (1).

The **composition** φ = (e¹₁e¹₂...e¹ₘ)·(e²₁e²₂...e²ₘ) is:
- If the second component returns true for η, φ(η) = true;
- If the second returns false but the first returns true, φ(η) = true;
- If both return false, φ(η) = false.

Define:
- TA₁ = {a | a is an aggressive truth assignment}
- TAₖ = {(a₁)(a₂)...(aₖ) | a₁,...,aₖ ∈ TA₁} for k ≥ 2
- TA∞ = ∪_{k≥1} TAₖ

**Metric on TA∞:** Define distance between atomic truth assignments:
- d(x*_i, ¬x*_j) = d(¬x*_j, x*_i) = (i+j)/(2^(i+j+2))
- d(x*_i, x*_j) = d(¬x*_i, ¬x*_j) = |i-j|/(2^(i+j+2))

For any e₁e₂...eₘ, e'₁e'₂...e'ₘ ∈ TA₁:
d(e₁e₂...eₘ, e'₁e'₂...e'ₘ) = Σ_{k=1}^∞ d(eₖ, e'ₖ)

This extends to TA∞ × TA∞ with appropriate weighted sums.

**Lemma 2.** d : TA∞ × TA∞ → [0,∞) is a metric and (TA∞, d) is a metric space.

---

## 6. Pseudo-algorithms

Suppose there are polynomial time algorithms on 3SAT_N. Define:
A = {f_ξ | f_ξ is a polynomial time algorithm on ∪_{n≥3}^∞ 3SAT_N(n)}

We prove A = ∅ by contradiction. Suppose A ≠ ∅.

For each a ∈ TA₁, define A_a = {f_ξ a | f_ξ ∈ A}, where:
f_ξ a(η) = true if a(η) = true, else f_ξ(η)

For f ∈ A, define:
- <f>₀ = {f}
- <f>ₖ = {f_α | α ∈ TAₖ} for k ≥ 1
- <f> = ∪_{k≥0} <f>ₖ

The metric d extends to <f> × <f>.

A sequence {f_n} in <f> is **Cauchy** if for any ε > 0 there exists N such that d(f_m, f_n) < ε for all m, n > N.

**Definition 1.** A set S is **compatible with the P versus NP problem** on ∪_{n≥3}^∞ 3SAT_N(n) if:
1. For any ρ ∈ S and η ∈ domain, ρ checks if η ∈ ∪_{s=1}^{3}(3,s)-SAT_N(n);
2. ρ is not an algorithm on the domain;
3. For any algorithm f_ξ, f_ξ ρ is an algorithm on the domain;
4. Some elements of S can generate an algorithm whose time complexity exceeds polynomial.

**Definition 2.** Any element of a compatible set S is called a **pseudo-algorithm**.

**Lemma 3.** For any n ≥ 3 and a ∈ TA₁, there exists η ∈ 3SAT_N(n) such that a(η) = true and a'(η) = false for any a' ∈ TA₁ not identical with a in the first n atomic truth assignments.

*Proof.* By explicit construction using groups of variables (x_k, x_{k+1}, x_{k+2}) with 4-clause gadgets that are satisfied exactly by the given assignment e_k. □

**Proposition 1.** TA₁ is compatible with the P versus NP problem on ∪_{n≥3}^∞ 3SAT_N(n).

---

## 7. Equivalence Classes

**Definition 3.** A bijective map π from ∪_{n≥3}^∞ 3SAT_N(n) to itself is **ordered** if π(3SAT_N(n)) = 3SAT_N(n) for all n ≥ 3.

**Definition 4.** Algorithms φ₁ and φ₂ are **equivalent** if there exists an ordered bijection π such that for every η, φ₁(η) and φ₂(π(η)) have the same implementation sequences.

**Definition 5.** Pseudo-algorithms ρ₁ and ρ₂ are **equivalent** if similarly for some ordered bijection π.

**Proposition 2.** Any a₁, a₂ ∈ TA₁ are equivalent.

*Proof.* Given a₁ = e¹₁e¹₂... and a₂ = e²₁e²₂..., define π by π(e¹_i) = e²_i. This extends to an ordered bijection on ∪_{n≥3}^∞ 3SAT_N(n), and under this map a₁ and a₂ have the same implementation sequences. □

**Lemma 4.** For any a₁, a₂ ∈ TA₁, the bijective ordered map π making them equivalent is unique.

**Lemma 5.** a₁a₂...aₘ ≡ b₁b₂...bₘ if and only if aᵢ ≡ bᵢ under the same map π, for i = 1,...,m.

**Corollaries 3–5** establish that equivalence is an equivalence relation.

**Proposition 3.** For each m ≥ 2, TAₘ has infinitely many equivalence classes.

*Proof.* For m = 2: let e⁻₀ be the negative generalized truth assignment. Define e⁻ₙ to agree with e⁻₀ everywhere except position n where it differs. Then e⁻_l e⁻₀ ≢ e⁻_k e⁻₀ for l ≠ k (by Lemma 5 and Lemma 4). □

---

## 8. Some Properties of Cauchy Sequences

**Definition 6.** A Cauchy sequence {f_n} in <f>₂ is **regular** if:
1. f_n = f_{a_n a_0} for n = 1,2,...;
2. a₀ is an arbitrarily given aggressive truth assignment;
3. a_n and a_{n+1} are identical on the first n atomic truth assignments;
4. a_n and a₀ are identical on atomic truth assignments e_{n+2}, e_{n+3}, ...

**Lemma 7.** Let {f_n} be a regular Cauchy sequence and ã₀ be the less efficient version of a₀. For any η, f_{ã₀ã₀} takes more steps than f_{a_k a_0} does for k = 1,2,...

*Proof.* By Lemma 1, ã₀ takes more steps than a₀. □

**Lemma 8.** Any element {f_n} in an equivalence class of ECS represents a polynomial time algorithm on ∪_{n≥3}^∞ 3SAT_N(n).

*Proof.* For any η ∈ 3SAT_N(n), define f_ζ(η) = f_{n-2}(η) = f_{a_{n-2} a_0}(η). Since f and a₀, a_n are polynomial time, f_{a_n a_0} is polynomial time. By Lemma 7, f_ζ takes fewer steps than f_{ã₀ã₀}, so f_ζ is also polynomial time. □

**Definition 8.** The algorithm f_ζ is the **representation** of {f_n}.

**Lemma 9.** If {f_n} ≢ {f'_n}, then f_ζ ≢ f'_ζ.

**Corollary 10.** If {f_n} ≢ {f'_n}, then f_ζ ≠ f'_ζ as algorithms.

---

## 9. Proof of Proposition 1

We prove TA₁ is compatible with the P versus NP problem.

Conditions (1), (2), (3) of Definition 1 follow from the definition of aggressive truth assignments.

For condition (4), construct an exponential time algorithm: let (e₁e₂...eₙ)^(2ⁿ) enumerate all 2ⁿ truth assignments on n variables. Then:

f₁ = f_{(e₁e₂e₃)^(2³)}, f₂ = f_{(e₁...e₄)^(2⁴)}, ..., fₖ = f_{(e₁...e_{k+2})^(2^{k+2})}, ...

This sequence is Cauchy with limit f_ξ where f_ξ(η) = f_{n-2}(η) = (e₁...eₙ)^(2ⁿ)(η) for η ∈ 3SAT_N(n).

By Lemma 3, there exists η_n ∈ 3SAT_N(n) such that (e₁...eₙ)^(2ⁿ)(η_n) = true but the algorithm must use all 2ⁿ aggressive truth assignments. Since η_n has 4n clauses, the time complexity is exponential in the length of η_n. □

---

## 10. Proof of the Main Result

We prove A = ∅. Suppose A ≠ ∅. Let f_ξ ∈ A. There are two cases:

**Case (1).** A_a ⊆ A for all a ∈ TA₁.

We prove ECS is uncountable. Suppose ECS is countable: list all equivalence classes as {f^1_n}, {f^2_n}, ...

For each k, pick a_k^k from the k-th element of {f^k_n}:
a^1_1 = e^1_1 e^1_2 ... e^1_k ..., a^2_2 = e^2_1 e^2_2 ... e^2_k ..., ...

Construct a diagonal sequence:
a₁ = ¬e^1_1 e₂ ¬x*₃ ... ¬x*ₖ ¬x*_{k+1} ...,
a₂ = ¬e^1_1 ¬e^2_2 e₃ ¬x*₄ ... ¬x*ₖ ¬x*_{k+1} ...,
...
aₖ = ¬e^1_1 ¬e^2_2 ... ¬e^k_k e_{k+1} ¬x*_{k+2} ...,

Define {f_n} = f_{a₁ a₀}, f_{a₂ a₀}, ..., f_{a_n a₀}, ...

This is a regular Cauchy sequence (Lemma 10), so {f_n} ∈ CS. But from the construction, f_{a_k a₀} ≠ f_{a^k_k a^k_0} for any k under the equivalence relation, so {f_n} is not in the list. Contradiction: ECS is uncountable.

Each element of ECS has a polynomial time representation (Lemma 8). Different equivalence classes have non-equivalent representations (Lemma 9) and hence different algorithms (Corollary 10). So A contains uncountably many algorithms — contradiction, since there are only countably many algorithms.

Therefore Case (1) is false.

**Case (2).** There exists a∗ ∈ TA₁ such that A_{a∗} ⊄ A.

Then there exists f_λ ∈ A such that f_λ a∗ ∉ A. But since a∗ is a polynomial time pseudo-algorithm and f_λ is polynomial time, f_λ a∗ is polynomial time, hence f_λ a∗ ∈ A. Contradiction.

Therefore Case (2) is false.

**Lemma 11.** A = ∅.

Since ∪_{n≥3}^∞ 3SAT_N(n) is NP-complete and has no polynomial time algorithm, we have:

**Theorem 3.** P ≠ NP.

---

## 11. Discussion

We can apply the new argument to 2SAT; however, no contradiction arises, so 2SAT remains in P. For 2SAT, aggressive truth assignments can use Aspvall, Plass and Tarjan's linear time algorithm as the second check. All aggressive truth assignments on 2SAT are linear time algorithms, so the pseudo-algorithm concept makes no sense for 2SAT.

---

## References

[1] S. Aaronson and A. Wigderson. Algebrization: A new barrier in complexity theory. *ACM Transactions on Computing Theory* 1(1):1–54, 2009.

[2] Aspvall, Bengt; Plass, Michael F.; Tarjan, Robert E. A Linear-time algorithm for testing the truth of certain quantified boolean formulas. *Information Processing Letters* 8(3):121–123, 1979.

[3] T. Baker, J. Gill, and R. Solovary. Relativizations of the P=?NP question. *SIAM J. Comput.*, 4:431–442, 1975.

[4] Cantor, Georg. Über eine Eigenschaft des Inbegriffes aller reelen algebraischen Zahlen, *Journal für die Reine und Angewandte Mathematik* 77, 258–262, 1874.

[5] Cantor, Georg. Über eine Elementare Frage der Mannigfaltigkeitslehre, *Jahresbericht der Deutschen Mathematiker-Vereinigung* 11, 75–78, 1890.

[6] Cook, Stephen A. The complexity of theorem-proving procedures, *Proc. 3rd Ann. ACM Symp. on Theory of Computing*, 151–158, 1971.

[7] Gurevich, Yuri. Sequential abstract state machines capture sequential algorithms, *ACM Transactions on Computational Logic*, Vol.1 No.1, 77–111, 2000.

[8] Hein, James L. 2010, *Discrete Structures, Logic, and Computability*, 3rd edition.

[9] Levin, Leonid A. Universal search problems (in Russian), *Problems of Information Transmission* 9(3): 265–266, 1973.

[10] Karp, Richard M. Reducibility among combinatorial problems, in R.E. Miller and J.W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, New York, 85–103, 1972.

[11] A. A. Razborov and S. Rudich. Natural proofs. *J. Comput. Sys. Sci.*, 55(1):24–35, 1997.

[12] Shamir, Adi. IP = PSPACE. *Journal of the ACM*, volume 39(4):869–877, 1992.

[13] Tovey, Craig A. A simplified satisfiability problem, *Discrete Appl. Math.* 8, 85–89, 1984.
