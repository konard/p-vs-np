# P is a proper subset of NP

**Author**: Jerrald Meek
**arXiv ID**: 0804.1079v12
**Date**: April 2008 (final revision: September 7, 2008)
**Source**: [arXiv:0804.1079](https://arxiv.org/abs/0804.1079)

---

## Abstract

The purpose of this article is to examine and limit the conditions in which the P complexity class could be equivalent to the NP complexity class. Proof is provided by demonstrating that as the number of clauses in a NP-complete problem approaches infinity, the number of input sets processed per computation performed also approaches infinity when solved by a polynomial time solution. It is then possible to determine that the only deterministic optimization of a NP-complete problem that could prove P = NP would be one that examines no more than a polynomial number of input sets for a given problem.

It is then shown that subdividing the set of all possible input sets into a representative polynomial search partition is a problem in the FEXP complexity class. The findings of this article are combined with the findings of other articles in this series of 4 articles. The final conclusion will be demonstrated that P ≠ NP.

---

## 1. Introduction

Stephen Cook described the importance of the P = NP question in his article *The P Versus NP Problem* [Cook 2006]. Cook noted that if P were to be proven equal to NP then the consequences would be devastating to cryptography, yet Cook added "it would also have stunning practical consequences of a more positive nature." These consequences could transform not only computer science, but mathematics in general.

Even if it turns out that P ≠ NP, Cook hoped that "every NP problem [may be] susceptible to a polynomial-time algorithm that works on 'most' inputs." [Cook 2006, p. 6]

In this article it will be shown that as the number of clauses in a NP-complete problem approaches infinity, the number of input sets processed per computation performed also approaches infinity when solved by a polynomial time solution. This will be used as the basis for proving the **P = NP Optimization Theorem** (Theorem 4.4), which will be used to develop the **P = NP Partition Theorem** (Theorem 5.1).

**Acknowledgments**: Several people who wish to remain anonymous have offered comments and suggestions which have improved this work. The author would also like to thank **Stephen Cook** who identified an incorrect premise in a previous version of this article which was related to the nature of non determinism. This contribution resulted in a major revision of the article. Although Cook has granted permission to mention his contribution, this does not imply any endorsement.

---

## 3. The Input Sets of NP-Complete Problems

### 3.1 Total number of possible K-SAT input sets

Let a K-SAT problem have k literals per clause and n clauses. Let x be a two dimensional set containing n sets each of which have k elements.

A CNF-K-SAT problem has the form:

```
[x₁₁ ∨ x₁₂ ∨ x₁₃ ∨ ... ∨ x₁ₖ] ∧
[x₂₁ ∨ x₂₂ ∨ x₂₃ ∨ ... ∨ x₂ₖ] ∧
[x₃₁ ∨ x₃₂ ∨ x₃₃ ∨ ... ∨ x₃ₖ] ∧
...
[xₙ₁ ∨ xₙ₂ ∨ xₙ₃ ∨ ... ∨ xₙₖ]
```

**Proof**: Clause 1 has k literals. If there is a second clause then there are k more literals, so there are 2k literals. If there is a third clause then there are k more literals, totaling 3k literals. So the total number of literals is nk.

We could then think of x as a binary number with kn digits. It then follows that the **number of possible input sets is 2^(kn)**.

### 3.2 Polynomial time computation rate of NP-complete problems

Let k be the number of literals in a clause such that k ≥ 3.
Let n be the number of clauses in a NP-complete class problem.
Let t(n) be a polynomial function representing the number of computations required for a problem in the complexity class NP-complete to be solved in polynomial time.

The number of input sets for a NP-complete problem as shown in Section 3.1 is 2^(kn).

**Proof**: r shall represent the number of input sets evaluated per computation performed:

```
r(n) = 2^(kn) / t(n)
```

If a NP-complete problem is solved in polynomial time by a search algorithm, then r(n) represents that the polynomial time solution must evaluate 2^(kn) input sets for every t(n) computations. This is the case provided that the method of solving the NP-complete problem checks all possible input sets.

---

## 4. The Limit of NP-Complete Polynomial Time Computation Rates

### 4.1 Exponential functions > polynomial functions

Let a be a constant such that a > 0.
Let p be a constant such that p > 0.
c = (ln a) which is also a constant.
f(x) = a^x
g(x) = ax^p + p

**Proof**: A pattern will be demonstrated by taking derivatives of f(x) and g(x):

```
f'(x) = (ln a)aˣ = caˣ
f''(x) = c(ln a)aˣ = c²aˣ
f'''(x) = c²(ln a)aˣ = c³aˣ

g'(x) = pax^(p-1)
g''(x) = p(p-1)ax^(p-2)
g'''(x) = p(p-1)(p-2)ax^(p-3)
```

As can be seen from this pattern, the (p-1)th derivative of f(x) would be c^(p-1)a^x, while the (p-1)th derivative of g(x) will be a constant.

Using L'Hôpital's Rule repeatedly:

```
lim(x→∞) f(x)/g(x) = lim(x→∞) c^(p-1)aˣ/CONSTANT = ∞
```

Therefore: **lim(x→∞) f(x)/g(x) = ∞ → f(x) > g(x)**

For any set of functions {f(x), g(x)} in which f(x) is exponential and g(x) is polynomial, there exists a number l such that any number n ≥ l will make the statement true that f(n) > g(n).

### 4.2 Limit at infinity of polynomial time computation rates for NP-complete problems

**Proof**: Let a be a number at which 2^(ak) > t(a). Section 4.1 indicates such a number must exist.

Using the definition of an infinite limit at infinity:

```
lim(n→∞) 2^(kn)/t(n) = ∞

2^(kn)/t(n) > N ← n > M
2^(kn)/t(n) > 1/t(n) ← n > a   (Set N = 1/t(n) and M = a)
t(n)·2^(kn)/t(n) > t(n)/t(n) ← n > a   (Multiply both sides by t(n))
2^(kn) > 1 ← n > a   (Cancel like terms)
```

Therefore: **lim(n→∞) r(n) = ∞**

Therefore, as the number of clauses in a NP-complete problem increases, the number of input sets that must be processed per computation performed will eventually exceed any finite limit.

### 4.3 The limitation of NP-complete optimizations

A Deterministic Turing Machine is limited to checking no more than one input per computation. Section 4.2 shows that when a polynomial time algorithm is used to check all possible input sets for a NP-Complete problem, the machine cannot be limited by the number of inputs checked per computation.

**THEOREM 4.4. P = NP Optimization Theorem.**

*The only deterministic optimization of a NP-complete problem that could prove P = NP would be one that can always solve a NP-complete problem by examining no more than a polynomial number of input sets for that problem.*

---

## 5. The Difficulty of Creating a Polynomial Optimization

### 5.1 Polynomial time under P = NP limitations

The term **"representative polynomial search partition"** will be used to indicate a partition from the set of all possible input sets such that the partition has a polynomial cardinality, and will contain at least one input set that results in a true evaluation if such an input set exists.

#### 5.1.1 The Form of a P = NP algorithm

**Proof**: The NP-Complete Optimization Theorem requires that any deterministic polynomial time algorithm for C must have the form:

```
(1) Set i = 1
(2) Find Pᵢ
(3) If Pᵢ ∈ α then halt in an accepting state.
(4) If Pᵢ ∉ α and i < |P| then increment i and continue at step 2.
(5) If Pᵢ ∉ α and i = |P| then halt in a non-accepting state.
```

This algorithm requires the longest time when A = ∅, or when |α| = 1 and P|P| ∈ α. In both cases the algorithm will be forced to find all elements of P. It is then the case that:

```
t_max = |P|(t_p + t_e)
```

It is known that |P| and t_e are products of polynomial functions. If P = NP then t_max must also be a product of a polynomial function. It is then the case that **t_p must be a polynomial function**.

#### 5.1.2 The complexity of finding the representative polynomial search partition

**Proof**: It should be a reasonable assumption that all elements of P share some quality in common, which is absent in all elements of S that are not elements of P. If this were not the case, then it would be impossible to discriminate the polynomial number of elements of P from the exponentially many other elements of S.

The algorithm for finding all elements of P by exhaustion is:

```
(1) Set i = 1
(2) If q ↦ Sᵢ then Sᵢ ∈ P
(3) If i < |S| then increment i and continue at step 2.
(4) If i = |S| then all elements of P have been found.
```

Notice that the algorithm iterates once for every element of S. It is then the case that the process of finding all elements of P requires an exponential number of iterations. It should be expected that an exponential number of iterations will require an exponential number of computations.

**This problem is then a member of a complexity class that could be described as FEXP.** This is a function problem that requires exponential time on a Deterministic Turing Machine.

#### 5.1.3 P ≠ NP when the representative polynomial search partition is found by exhaustion

**Proof**: If a NP-complete problem is solved in deterministic exponential time, then the algorithm may iterate through every element of the set of all possible inputs. However, the algorithm also can stop searching when the algorithm finds an input set that evaluates true.

In the previous section it was shown that the process for finding the elements of the representative polynomial search partition by exhaustion requires searching all elements of the set of all possible inputs. Finding all elements of the search partition does not end when an element is found, because there may be more. It is therefore the case that the algorithm for finding all elements of the representative polynomial search partition must always require the entire duration of its worst case time (if the entire partition is found).

Therefore: **t_p ≥ t_s**

### 5.2 The limitation of NP-complete search partitioning

Section 5.1.1 shows that a deterministic polynomial time solution for a NP-complete problem must produce a representative polynomial search partition in deterministic polynomial time. Section 5.1.3 indicates that evaluating all elements of the set of all possible inputs to find elements of the search partition results in a NP-complete problem being solved in deterministic exponential time.

**THEOREM 5.1. P = NP Search Partition Theorem.**

*The only deterministic search optimization of a NP-complete problem that could prove P = NP would be one that can always find a representative polynomial search partition by examining no more than a polynomial number of input sets from the set of all possible input sets.*

---

## 6. Examples of NP-Complete Solutions

The set of all possible input sets for a NP-complete problem is exponential in size. If a deterministic polynomial time algorithm is to be found, then a representative polynomial search partition must be found in deterministic polynomial time. For a search partition to be found in deterministic polynomial time, then a search partition for that search partition must be found in deterministic polynomial time. **This circular argument means that finding a deterministic polynomial time algorithm for a NP-complete problem can be done only if a deterministic polynomial time algorithm for that problem already exists.**

---

## 7. Conclusion

The final conclusion is drawn from the following premises:

(1) The complexity class of P is the class of problems that can be solved in polynomial time by a Deterministic Turing Machine.

(2) The P = NP Optimization Theorem requires that an algorithm that solves a NP-complete problem in deterministic polynomial time can examine no more than a polynomial-sized search partition, and must find this partition in deterministic polynomial time.

(3) Some NP-complete problems can only have a deterministic polynomial time solution if the SAT problem has a deterministic polynomial time solution. [Meek Article 2 2008]

(4) SAT does not have a deterministic polynomial time solution. [Meek Article 4 2008]

### 7.1 P is a proper subset of NP

Because some NP-complete problems are dependant upon SAT to produce a deterministic polynomial time solution for them, and because SAT does not have a deterministic polynomial time solution, then P is a proper subset of NP. **P ≠ NP.**

**Q.E.D.**

---

## 8. Version History

The author has decided to include a record of the version history for this article to acknowledge that after the original draft, it has taken on an "organic life" and been revised several times.

**arXiv Current Version** (6 Sep 2008):
- Reference to [Meek Article 3 2008] added
- Revision of introduction, conclusion, and abstract
- Minor formatting changes

**Key Previous Versions**:
- **Version 7** (22 Apr 2008): Major revision with more formal approach
- **Version 5** (16 Apr 2008): Major change due to invalid theorem - NP-Complete Optimization Theorem abandoned
- **Version 1** (7 Apr 2008): Initial arXiv submission

The paper underwent **12 revisions** between April and September 2008.

---

## References

Cook, S. 2006. The P Versus NP Problem. *The millennium prize problems*, 87–104, Clay Math. Inst.

Horowitz, E. and Sahni, S. 1974. Computing partitions with applications to the knapsack problem. *J. Assoc. Comput. Mach.*

Karp, R. 1972. Reducibility among combinatorial problems. *Complexity of computer computations, Proc. Sympos., IBM Thomas J. Watson Res. Center.*

Meek, J. 2008. Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem. arXiv:0805.0517 (Article 2 in series of 4)

Meek, J. 2008. Independence of P vs. NP in regards to oracle relativizations. arXiv:0805.2170 (Article 3 in series of 4)

Meek, J. 2008. Analysis of the postulates produced by Karp's Theorem. arXiv:0808.3222 (Article 4 in series of 4)
