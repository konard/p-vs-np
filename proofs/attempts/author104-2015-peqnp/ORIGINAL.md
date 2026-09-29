# Solution of P versus NP Problem

**Author:** Frank Vega
**Year:** 2015
**HAL Archive:** hal-01161668
**Source:** https://hal.science/hal-01161668v1
**Preprint submitted:** 8 Jun 2015

---

## Abstract

The P versus NP problem is one of the most important and unsolved problems in computer science. This consists in knowing the answer of the following question: Is P equal to NP? This incognita was first mentioned in a letter written by Kurt Gödel to John von Neumann in 1956. However, the precise statement of the P versus NP problem was introduced in 1971 by Stephen Cook in a seminal paper. We consider a new complexity class, called equivalent-P, which has a close relation with this problem. The class equivalent-P has those languages that contain ordered pairs of instances, where each one belongs to a specific problem in P, such that the two instances share a same solution, that is, the same certificate. We demonstrate that equivalent-P = NP and equivalent-P = P. In this way, we find the solution of P versus NP problem, that is, P = NP.

---

## 1 Introduction

The P versus NP problem is a major unsolved problem in computer science. This problem was introduced in 1971 by Stephen Cook [2]. It is considered by many to be the most important open problem in the field [4]. It is one of the seven Millennium Prize Problems selected by the Clay Mathematics Institute to carry a US$1,000,000 prize for the first correct solution.

The argument made by Alan Turing in the twentieth century states that for any algorithm we can create an equivalent Turing machine [10]. There are some definitions related with this model such as the deterministic or nondeterministic Turing machine. A deterministic Turing machine has only one next action for each step defined in its program or transition function [9]. A nondeterministic Turing machine can contain more than one action defined for each step of the program, where this program is not a function, but a relation [9].

Another huge advance in the last century was the definition of a complexity class. A language L over an alphabet is any set of strings made up of symbols from that alphabet [3]. A complexity class is a set of problems, which are represented as a language, grouped by measures such as the running time, memory, etc [3].

In computational complexity theory, the class P consists in all those decision problems (defined as languages) that can be decided on a deterministic Turing machine in an amount of time that is polynomial in the size of the input; the class NP consists in all those decision problems whose positive solutions can be verified in polynomial-time given the right information, or equivalently, that can be decided on a nondeterministic Turing machine in polynomial-time [7].

The biggest open question in theoretical computer science concerns the relationship between those two classes:

> Is P equal to NP?

In a 2002 poll of 100 researchers, 61 believed the answer to be no, 9 believed the answer is yes, and 22 were unsure; 8 believed the question may be independent of the currently accepted axioms and so impossible to prove or disprove [6].

There is an important complexity class called NP-complete [7]. The NP-complete problems are a set of problems to which any other NP problem can be reduced in polynomial-time, but whose solution may still be verified in polynomial-time [7]. In addition, there is another important complexity class called P-complete [9]. The P-complete problems are a set of problems to which any other P problem can be reduced in logarithmic-space, but they still remain in P [9]. We shall define a new complexity class that we called equivalent-P (see the Abstract) and denoted as ∼P. We shall show that there is an NP-complete problem in ∼P and a P-complete problem in ∼P. Moreover, we shall prove the complexity class ∼P is closed under reductions. Since P and NP are also closed under reductions, then we can conclude that P = NP.

---

## 2 Theoretical Framework

### 2.1 NP-complete class

We say that a language L₁ is polynomial-time reducible to a language L₂, written L₁ ≤ᵖ L₂, if there exists a polynomial-time computable function f : {0,1}* → {0,1}* such that for all x ∈ {0,1}*,

> x ∈ L₁ if and only if f(x) ∈ L₂.  **(2.1)**

There is an important complexity class called NP-complete [7]. A language L ⊆ {0,1}* is NP-complete if

- L ∈ NP, and
- L' ≤ᵖ L for every L' ∈ NP.

Furthermore, if L is a language such that L' ≤ᵖ L for some L' ∈ NP-complete, then L is NP-hard [3]. Moreover, if L ∈ NP, then L ∈ NP-complete [3].

One of the first discovered NP-complete problems was SAT [5]. An instance of SAT is a Boolean formula φ which is composed of

- Boolean variables: x₁, x₂, ...;
- Boolean connectives: Any Boolean function with one or two inputs and one output, such as ∧(AND), ∨(OR), ¬(NOT), →(implication), ↔(if and only if); and
- parentheses.

A truth assignment for a Boolean formula φ is a set of values for the variables of φ and a satisfying truth assignment is a truth assignment that causes it to evaluate to true. A formula with a satisfying truth assignment is a satisfiable formula. The SAT asks whether a given Boolean formula is satisfiable.

One convenient language is 3CNF satisfiability, or 3SAT [3]. We define 3CNF satisfiability using the following terms. A literal in a Boolean formula is an occurrence of a variable or its negation. A Boolean formula is in conjunctive normal form, or CNF, if it is expressed as an AND of clauses, each of which is the OR of one or more literals. A Boolean formula is in 3-conjunctive normal form, or 3CNF, if each clause has exactly three distinct literals.

For example, the Boolean formula

> (x₁ ∨ ¬x₁ ∨ ¬x₂) ∧ (x₃ ∨ x₂ ∨ x₄) ∧ (¬x₁ ∨ ¬x₃ ∨ ¬x₄)  **(2.2)**

is in 3CNF. The first of its three clauses is (x₁ ∨ ¬x₁ ∨ ¬x₂), which contains the three literals x₁, ¬x₁, and ¬x₂. In 3SAT, we are asked whether a given Boolean formula φ in 3CNF is satisfiable.

Many problems can be proved that belong to NP-complete by a polynomial-time reduction from 3SAT [5]. For example, the problem ONE-IN-THREE 3SAT defined as follows: Given a Boolean formula φ in 3CNF, is there a truth assignment such that each clause in φ has exactly one true literal?

### 2.2 P-complete class

We say that a language L₁ is logarithmic-space reducible to a language L₂, if there exists a logarithmic-space computable function f : {0,1}* → {0,1}* such that for all x ∈ {0,1}*,

> x ∈ L₁ if and only if f(x) ∈ L₂.  **(2.3)**

The logarithmic space reduction is frequently used for P and below [9].

There is an important complexity class called P-complete [9]. A language L ⊆ {0,1}* is P-complete if

- L ∈ P, and
- L' is logarithmic-space reducible to L for every L' ∈ P.

One of the P-complete problems is HORNSAT [9]. We say that a clause is a Horn clause if it has at most one positive literal [9]. That is, all its literals, except possibly for one, are negations of variables. An instance of HORNSAT is a Boolean formula φ in CNF which is composed only of Horn clauses [9].

For example, the Boolean formula

> (¬x₂ ∨ x₃) ∧ (¬x₁ ∨ ¬x₂ ∨ ¬x₃ ∨ ¬x₄) ∧ (x₁)  **(2.4)**

is a conjunction of Horn clauses. The HORNSAT asks whether an instance of this problem is satisfiable [9].

### 2.3 Problems in P

Another special case is the class of problems where each clause contains XOR (i.e. exclusive or) rather than (plain) OR operators. This is in P, since an XOR-SAT formula can also be viewed as a system of linear equations mod 2, and can be solved in cubic time by Gaussian elimination [8]. We denote the XOR function as ⊕. The XOR 3SAT problem will be equivalent to XOR-SAT, but the clauses in the formula have exactly three distinct literals. Since a ⊕ b ⊕ c evaluates to true if and only if exactly 1 or 3 members of {a, b, c} are true, each solution of the ONE-IN-THREE 3SAT problem for a given 3CNF formula is also a solution of the XOR 3SAT problem and in turn each solution of XOR 3SAT is a solution of 3SAT.

In addition, a Boolean formula is in 2-conjunctive normal form, or 2CNF, if it is in CNF and each clause has exactly two distinct literals. There is a problem called 2SAT, where we asked whether a given Boolean formula φ in 2CNF is satisfiable. This problem is in P [1].

---

## 3 Definition of ∼P

Let L be a language and M a Turing machine. We say that M is a verifier for L if L can be written as

> L = {x : (x, y) ∈ R for some y}  **(3.1)**

where R is a polynomially balanced relation decided by M [9]. According to Cook's Theorem, a language L is in NP if and only if it has a polynomial-time verifier [9].

**Definition 3.1.** Given two languages, L₁ and L₂, and two Turing machines, M₁ and M₂, such that L₁ ∈ P and L₂ ∈ P where M₁ and M₂ are the verifiers of L₁ and L₂ respectively, we say that a language L belongs to ∼P if,

> L = {(x, y) : ∃z such that M₁(x, z) = "yes" and M₂(y, z) = "yes" where x ∈ L₁ and y ∈ L₂}.  **(3.2)**

We will call the complexity class ∼P as "equivalent-P".

---

## 4 Reduction in ∼P

There is a different kind of reduction for ∼P: The e-reduction.

**Definition 4.1.** Given two languages L₁ and L₂, such that the instances of L₁ and L₂ are ordered pairs of strings, we say that a language L₁ is e-reducible to a language L₂, written L₁ ≤∼ L₂, if there exist two logarithmic-space computable functions f : {0,1}* → {0,1}* and g : {0,1}* → {0,1}* such that for all x ∈ {0,1}* and y ∈ {0,1}*,

> (x, y) ∈ L₁ if and only if (f(x), g(y)) ∈ L₂.  **(4.1)**

We say that a complexity class C is closed under reductions if, whenever L₁ is reducible to L₂ and L₂ ∈ C, then also L₁ ∈ C [9].

**Theorem 4.2.** ∼P is closed under reductions.

**Proof.** Let L and L' be two arbitrary languages, where their instances are ordered pairs of strings, L ≤∼ L' and L' ∈ ∼P. We shall show that L is in ∼P too. By definition of ∼P, there are two languages L'₁ and L'₂, such that for each (v, w) ∈ L' we have that v ∈ L'₁ and w ∈ L'₂ where L'₁ ∈ P and L'₂ ∈ P. Moreover, there are two Turing machines M'₁ and M'₂ which are the verifiers of L'₁ and L'₂ respectively, and for each (v, w) ∈ L' exists a polynomially bounded certificate z such that M'₁(v, z) = "yes" and M'₂(w, z) = "yes". Besides, by definition of e-reduction, there exist two logarithmic-space computable functions f : {0,1}* → {0,1}* and g : {0,1}* → {0,1}* such that for all x ∈ {0,1}* and y ∈ {0,1}*,

> (x, y) ∈ L if and only if (f(x), g(y)) ∈ L'.  **(4.2)**

From this preliminary information, we can conclude there exist two languages L₁ and L₂, such that for each (x, y) ∈ L we have that x ∈ L₁ and y ∈ L₂ where L₁ ∈ P and L₂ ∈ P. Indeed, we could define L₁ and L₂ as the instances f⁻¹(v) and g⁻¹(w) respectively, such that f⁻¹(v) ∈ L₁ and g⁻¹(w) ∈ L₂ if and only if v ∈ L'₁ and w ∈ L'₂. Certainly, for all x ∈ {0,1}* and y ∈ {0,1}*, we can decide x ∈ L₁ or y ∈ L₂ in polynomial-time just verifying that f(x) ∈ L'₁ or g(y) ∈ L'₂ respectively, because L'₁ ∈ P, L'₂ ∈ P and SPACE(log n) ∈ P [9]. Furthermore, there exist two Turing machines M₁ and M₂ which are the verifiers of L₁ and L₂ respectively, and for each (x, y) ∈ L exists a polynomially bounded certificate z such that M₁(x, z) = "yes" and M₂(y, z) = "yes". Indeed, we could know whether M₁(x, z) = "yes" and M₂(y, z) = "yes" for some polynomially bounded string z just verifying whether M'₁(f(x), z) = "yes" and M'₂(g(y), z) = "yes". That is, we may have that M₁(x, z) = M'₁(f(x), z) and M₂(y, z) = M'₂(g(y), z), because we can evaluate f(x) and g(y) in polynomial-time since SPACE(log n) ∈ P [9]. In this way, we have proved that L ∈ ∼P. □

---

## 5 ∼P = NP

We define ∼ONE-IN-THREE 3SAT as follows,

> ∼ONE-IN-THREE 3SAT = {(φ, φ) : φ ∈ ONE-IN-THREE 3SAT}.  **(5.1)**

It is trivial to see the ∼ONE-IN-THREE 3SAT problem remains in NP-complete (see Section 2).

**Definition 5.1.** 3XOR-2SAT is a problem in ∼P, such that if (ψ, φ) ∈ 3XOR-2SAT, then ψ ∈ XOR 3SAT and φ ∈ 2SAT. That is, the instances of XOR 3SAT and 2SAT (see Section 2) that can have the same satisfying truth assignment (with the same variables).

**Theorem 5.2.** ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT.

**Proof.** Given an arbitrary Boolean formula φ in 3CNF of m clauses, we will iterate for each clause cᵢ = (x ∨ y ∨ z) in φ, where x, y and z are literals, and create the following formulas,

> Qᵢ = (x ⊕ y ⊕ z)  **(5.2)**

> Pᵢ = (¬x ∨ ¬y) ∧ (¬y ∨ ¬z) ∧ (¬x ∨ ¬z).  **(5.3)**

Since Qᵢ evaluates to true if and only if exactly 1 or 3 members of {x, y, z} are true and Pᵢ evaluates to true if and only if exactly 1 or 0 members of {x, y, z} are true, we obtain the clause cᵢ has exactly one true literal if and only if both formulas Qᵢ and Pᵢ are satisfiable with the same truth assignment. Hence, we can create the ψ and φ formulas as the conjunction of the Qᵢ and Pᵢ formulas for every clause cᵢ in φ, that is, ψ = Q₁ ∧ ... ∧ Qₘ and φ = P₁ ∧ ... ∧ Pₘ. Finally, we obtain that,

> (φ, φ) ∈ ∼ONE-IN-THREE 3SAT if and only if (ψ, φ) ∈ 3XOR-2SAT.  **(5.4)**

In addition, there exist two logarithmic-space computable functions f : {0,1}* → {0,1}* and g : {0,1}* → {0,1}* such that f(<φ>) = <ψ> and g(<φ>) = <φ>. Indeed, we only need a logarithmic-space to analyze at once each clause cᵢ in the input φ and generate Qᵢ or Pᵢ to the output, since the complexity class SPACE(log n) does not take the length of the input and the output into consideration [9]. □

**Theorem 5.3.** ∼P = NP.

**Proof.** If there is an NP-complete problem reducible to a problem in ∼P, then this NP-complete problem will be in ∼P, and thus, ∼P = NP, because ∼P is closed under reductions (see Theorem 4.2) and NP too [9]. Therefore, this is a direct consequence of Theorem 5.2. □

---

## 6 P = NP

We define ∼HORNSAT as follows,

> ∼HORNSAT = {(φ, φ) : φ ∈ HORNSAT}.  **(6.1)**

It is trivial to see the ∼HORNSAT problem remains in P-complete (see Section 2).

**Theorem 6.1.** ∼HORNSAT ∈ ∼P.

**Proof.** The ∼HORNSAT problem complies with all the properties of a language in ∼P. That is, for each (φ, φ) ∈ ∼HORNSAT, the Boolean formula φ belongs to a language in P, that is, the same HORNSAT. In addition, the verifier M of HORNSAT complies that always exists a polynomially bounded certificate z when φ is satisfiable, that is the satisfying truth assignment of φ, such that M(φ, z) = "yes". Certainly, we can prove this result, because any ordered pair of Boolean formulas in ∼HORNSAT can share the same certificate due to they are equals. □

**Theorem 6.2.** ∼P = P.

**Proof.** If a P-complete is in ∼P, then ∼P = P, because ∼P is closed under reductions (see Theorem 4.2) and P too [9]. Therefore, this is a direct consequence of Theorem 6.1. □

**Theorem 6.3.** P = NP.

**Proof.** Since ∼P = NP and ∼P = P as result of Theorems 5.3 and 6.2, then we can conclude that P = NP. □

---

## References

1. BENGT ASPVALL, MICHAEL F. PLASS, AND ROBERT E. TARJAN: A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas. *Information Processing Letters*, 8(3):121–123, 1979. [doi:10.1016/0020-0190(79)90002-4]
2. STEPHEN A. COOK: The complexity of Theorem Proving Procedures. In *Proceedings of the 3rd Annual ACM Symposium on the Theory of Computing (STOC'71)*, pp. 151–158. ACM Press, 1971.
3. THOMAS H. CORMEN, CHARLES ERIC LEISERSON, RONALD L. RIVEST, AND CLIFFORD STEIN: *Introduction to Algorithms*. MIT Press, 2 edition, 2001.
4. LANCE FORTNOW: The Status of the P versus NP Problem. *Communications of the ACM*, 52(9):78–86, 2009. [doi:10.1145/1562164.1562186]
5. MICHAEL R. GAREY AND DAVID S. JOHNSON: *Computers and Intractability: A Guide to the Theory of NP-Completeness*. San Francisco: W. H. Freeman and Company, 1 edition, 1979.
6. WILLIAM I. GASARCH: The P=?NP poll. *SIGACT News*, 33(2):34–47, 2002.
7. ODED GOLDREICH: *P, NP, and NP-Completeness*. Cambridge: Cambridge University Press, 2010.
8. CRISTOPHER MOORE AND STEPHAN MERTENS: *The Nature of Computation*. Oxford University Press, 2011.
9. CHRISTOS H. PAPADIMITRIOU: *Computational complexity*. Addison-Wesley, 1994.
10. ALAN M. TURING: On Computable Numbers, with an Application to the Entscheidungsproblem. *Proceedings of the London Mathematical Society*, 42:230–265, 1936.

---

## Author

Frank Vega  
La Portada, Cotorro  
Havana, Cuba
