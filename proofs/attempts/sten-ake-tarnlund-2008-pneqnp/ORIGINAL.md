# Original Paper: P is not equal to NP

**Author:** Sten-Ake Tarnlund
**Year:** 2008 (arXiv:0810.5056v1, submitted October 28, 2008)
**arXiv ID:** [arXiv:0810.5056](https://arxiv.org/abs/0810.5056)
**Subject Classification:** Computational Complexity (cs.CC); Logic in Computer Science (cs.LO)
**Woeginger's List:** Entry #48

---

## Abstract

SAT ∉ P is true, and provable in a simply consistent extension B' of a first order theory **B** of computing, with a single finite axiom B characterizing a universal Turing machine. Therefore P ≠ NP is true, and provable in a simply consistent extension B'' of **B**.

---

## 1. Introduction

SAT ∉ P is true, theorem 1, and provable, corollary 9, in a simply consistent extension B' of a first order theory **B** of computing, with a single finite axiom B characterizing a universal Turing machine. Therefore, by the Cook-Levin theorem (SAT ∈ P ≡ P = NP, Cook 1971, Levin 1973), P ≠ NP is true, theorem 2, and provable, corollary 10, in a simply consistent extension B'' of theory **B**.

SAT is the set of satisfiable propositional formulas. P and NP are sets of classes of problems of polynomial time complexity for deterministic and nondeterministic Turing machines respectively.

The chief idea of the proof of theorem 1 is a relationship between computing time and proof complexity, in fact, the principal lemma 3, which essentially is developed from axiom B. First, there is a relationship between a formal proof in theory **B**, and a formula in propositional logic. However, lemma 3 gives more i.e., the number of tapehead moves of a deterministic Turing machine computing unsatisfiability of ¬F expressed as a simple formula in propositional logic, from which the tautology F is deducible. More precisely: if there is a deterministic Turing machine i ∈ U that computes unsatisfiability of ¬F in computing time n polynomial in the size of F then Y(i, F, n), for a sufficiently large tautology F.

More to the point, by definition 20, Y(i, F, n) is equivalent to:

```
(Q₀ ⊃ F) ∧ Qₙ ∧ ⋀₁≤k≤n (Qₖ ⊃ Qₖ₋₁)  some single letters Q₀,...,Qₙ   (1)
```

In propositional logic there is a formal deduction of the tautology F in polynomial time in the size of F if Y(i, F, n) is true. There is now an indirect proof of theorem 1.

Assume that

```
SAT ∈ P.                                                                    (2)
```

By lemma 3, and a sufficiently large pigeonhole formula PFₘ,

```
Y(i, PFₘ, n) and n ≤ c·|PFₘ|^q  some c q ∈ ℕ  i ∈ U  a sufficiently large m.  (3)
```

Thus, by (1),

```
(Q₀ ⊃ PFₘ) ∧ Qₙ ∧ ⋀₁≤k≤n (Qₖ ⊃ Qₖ₋₁)  some single letters Q₀,...,Qₙ.    (4)
```

By Robinson's resolution, and (3) - (4), no more than c·|PFₘ|^q resolvents are constructed in the deduction of PFₘ from (4), and the size of the formal deduction is polynomial in the size of PFₘ. Therefore

```
⊢_R PFₘ, with a polynomial size of the deduction in the size of PFₘ.         (5)
```

Hence, a contradiction between (5), Haken's theorem (every resolution proof of PFₙ contains at least cⁿ different clauses for c > 1 some c ∈ ℝ any sufficiently large n ∈ ℕ), and the fact that theory **B** is simply consistent i.e., has no contradiction, for the subset of the deterministic Turing machines that compute satisfiability or unsatisfiability of propositional formulas, corollary 2.

Thus

```
SAT ∉ P.                                                                    (6)
```

It remains to lay down the first order theory **B** of computing, with axiom B, and to prove the principal lemma 3. Then a proof of theorem 1 follows in the proof (meta) theory of **B**, as outlined in (2) - (6).

---

## 2. A theory of computing

Before applying the axiomatic method to computing complexity, a first order theory **B** of computing, with a single finite axiom B characterizing a universal Turing machine, is presented.

Syntactically, there are two predicate symbols of **B** written T(i, a, u), and U(x, s, z, q, j, i, u). In addition, one function symbol . in infix notation x.y.

A Turing machine has a finite supply of arbitrary constant symbols, for example, the alphabetic symbols A, a, B, b, ..., the natural numbers, and the symbols of propositional logic. For convenience, there is at least a subset

```
{∅, 0, 1, ⊔} ⊆ K,                                                          (7)
```

where K is a finite set of constant symbols, and ⊔ a blank symbol.

There are six sets in **B**.

A finite set

```
Q ⊂ ℕ of states,                                                            (8)
```

where 0 is the halt state and 1 the start state.

A finite set S of symbols,

```
S for { u : u ∈ K ∨ (u = r.∅ ∨ u = ∅.r) ∧ r ∈ K}.                         (9)
```

A set D of moves of the tapehead of a Turing machine,

```
D for {0, 1},                                                               (10)
```

where 0 is a move to the left and 1 a move to the right.

There is a finite arbitrary large two-way tape, with a left and right tape having an element between them at the tapehead. Initially, the two-way tape has an empty left tape, the input on the right tape, and the element between them has the symbol ∅. When a computation starts the tapehead reads the symbol ∅.

There are two sets L and L' of lists, representing the right tape, and left tape respectively:

```
L(∅) ∧ ∀ (s ∈ S ∧ L(z) ⊃ L(s.z)), and                                     (11)
L'(∅) ∧ ∀ (s ∈ S ∧ L'(z) ⊃ L'(z.s))                                       (12)
```

Then,

```
L for {u : L(u)}.                                                           (13)
L' for {u : L'(u)}.                                                         (14)
```

A set M ⊂ L of codes of Turing machines:

```
M(∅) ∧ ∀ (p q ∈ Q ∧ r s ∈ S ∧ d ∈ D ∧ M(z) ⊃ M(p.s.q.r.d.z)).           (15)
```

Then the set of codes of Turing machines,

```
M for {u : M(u)}.                                                           (16)
```

**Definition 1** The set PROP of atomic propositional formulas of theory **B** has the elements U(x, s, z, q, j, i, u), and T(i, a, u) i j ∈ M a z ∈ L x u ∈ L' q ∈ Q s ∈ S.

**Definition 2** The set ATOM of atomic formulas of theory **B** has as members the elements in PROP, and an atomic formula constructed by substituting a variable for a term in an atomic propositional formula in PROP.

**Definition 3** The set of formulas of theory **B** has as members the elements in ATOM, and an element constructed by the formation rules of predicate calculus from elements in ATOM.

Semantically, the infix function symbol and the predicate symbols denote two functions and two relations.

- T(i, a, u) shall mean Turing machine i with input a computes an output u and then halts for i ∈ M a ∈ L u ∈ L'.
- U(x, s, z, q, j, i, u) shall mean Turing machine i computes u and then halts, where x.s.z is the two-way tape of i, s is a symbol (at the tapehead), x is the left tape, z is the right tape, i is in state q, and has an auxiliary code j, for i j ∈ M s ∈ S z ∈ L q ∈ Q x u ∈ L'.

### Axiom 1 (B)

```
∀ T(i, a, u) ⊃ U(∅, ∅, a.∅, 1, i, i, u)   i ∈ M a ∈ L u ∈ L'.            (17)
∀ U(∅, ∅, a.∅, 1, i, i, u) ⊃ T(i, a, u)   a ∈ L i ∈ M u ∈ L'.            (18)
∀ U(x, s, z, 0, i, i, x)   x ∈ L' s ∈ S z ∈ L i ∈ M.                     (19)
∀ U(x, v, r.z, p, i, i, u) ⊃ U(x.v, s, z, q, q.s.p.r.0.j, i, u)          (20)
  x u ∈ L' v r s ∈ S z ∈ L p q ∈ Q i j ∈ M.
∀ U(x.r, v, z, p, i, i, u) ⊃ U(x, s, v.z, q, q.s.p.r.1.j, i, u)          (21)
  x u ∈ L' r v s ∈ S z ∈ L p q ∈ Q i j ∈ M.
∀ U(x, s, z, q, j, i, u) ⊃ U(x, s, z, q, q'.s'.p.r.d.j, i, u)            (22)
  x u ∈ L' s s' r ∈ S z ∈ L q q' p ∈ Q j i ∈ M d ∈ D.
```

Sentences (17)-(18) give equivalence between T(i,a,u) and the concrete representation. Sentence (19) is the halt condition. Sentences (20)-(21) handle left/right moves. Sentence (22) handles quintuple searching.

**Definition 4** D = {i : i has no quintuples q.s.p.r.d and q.s.p'.r'.d' and ¬(p = p' ∧ r = r' ∧ d = d') for i ∈ M}.

**Lemma 1** ∃uT(i, a, u) ⊃ ⊢ B → ∃uT(i, a, u) any i ∈ M a ∈ L.

**Definition 5** A Turing machine computation for a formal proof in theory **B**.

---

## 3. Computing time

**Definition 6** H(⊢ B → ∃uT(i, a, u), n) for there is a formal proof of the sequent B → ∃uT(i, a, u) in G4 with n moves of the tapehead of a Turing machine i with an input a computing an output, any i ∈ M a ∈ L n ∈ ℕ.

**Definition 7** |a| for the number of symbols of a ∈ L.

**Definition 8** p(a) for c·|a|^q some c q ∈ ℕ any a ∈ L.

**Definition 9** ⊢ B → ∃uT(i, a, u) in p(a) for H(⊢ B → ∃uT(i, a, u), n) ∧ n ≤ c·|a|^q any i ∈ M some c q ∈ ℕ any a ∈ L some n ∈ ℕ.

**Definition 10** F for the set of formulas of propositional logic.

**Definition 11** SAT for {F : F ∈ F ∧ ⊭ ¬F}.

**Definition 12** TAUT for {F : F ∈ F ∧ ⊨ F}.

**Definition 13** T(s, a, u) for a = F.∅ ∧ ((u = ∅.0 ∧ ⊭ ¬F) ∨ (u = ∅.1 ∧ ⊨ ¬F)) any a ∈ L F ∈ F u ∈ L.

**Definition 14** U for { i : ∃u(T(i, a, u) ∧ T(s, a, u)) ∧ i ∈ D ∧ any a ∈ L }.

**Corollary 1** T(i, ¬F.∅, ∅.1) ≡ F any i ∈ U any F ∈ TAUT.

**Corollary 2** ⊢ B → ∃u T(i, a, u) ∧ ¬∃u T(i, a, u) no i ∈ U a ∈ L.

**Corollary 3** ⊢ B → ∃u T(i, a, u) ≡ ∃u T(i, a, u) any i ∈ U a ∈ L.

**Definition 15** SAT ∈ P for ⊢ B → ∃u T(i, F.∅, u) in p(F) some i ∈ U any F ∈ F.

**Corollary 4** ⊢ B → T(i, ¬F.∅, ∅.1) ≡ ⊨ → F any i ∈ U F ∈ F.

**Corollary 5** If SAT ∈ P then ⊢ B → T(i, ¬F.∅, ∅.1) in p(F) some i ∈ U any F ∈ TAUT.

---

## 4. Computing time and proof complexity

A relationship between computing time and proof complexity is established in the principal lemma 3, using lemma 2, and axiom B.

**Definition 16** V(i, F, n) for

```
(U(x₀, s₀, z₀, q₀, i, i, ∅.1) ⊃ T(i, ¬F.∅, ∅.1)) ∧                      (35)
U(∅.1, sₙ, zₙ, 0, i, i, ∅.1) ∧                                            (36)
⋀₁≤m≤n ((U(xₘ, sₘ, zₘ, qₘ, i, i, ∅.1) ⊃                                  (37)
  U(xₘ₋₁, sₘ₋₁, zₘ₋₁, qₘ₋₁, jₘ₋₁, i, ∅.1)) ∧
  (U(xₘ₋₁, sₘ₋₁, zₘ₋₁, qₘ₋₁, jₘ₋₁, i, ∅.1) ⊃
  U(xₘ₋₁, sₘ₋₁, zₘ₋₁, qₘ₋₁, i, i, ∅.1)))
any i ∈ U F ∈ TAUT n ∈ ℕ
```

**Lemma 2** H(⊢ B → T(i, ¬F.∅, ∅.1), n) ⊃ V(i, F, n) any i ∈ U F ∈ TAUT n ∈ ℕ.

**Definition 17** Qₘ for U(xₘ, sₘ, zₘ, qₘ, i, i, ∅.1) any i ∈ U ... some single letters Qₘ ∈ F.

**Definition 18** Rₘ₊₁ for U(xₘ, sₘ, zₘ, qₘ, jₘ, i, ∅.1) any i ∈ U ... some single letters Rₘ₊₁ ∈ F.

**Definition 19** W(i, F, n) for Qₙ ∧ ⋀₁≤m≤n (Rₘ ⊃ Qₘ₋₁) ∧ (Qₘ ⊃ Rₘ) ∧ (Q₀ ⊃ T(i, ¬F.∅, ∅.1)) any i ∈ U F ∈ TAUT n ∈ ℕ some single letters Q₀,...,Qₙ, R₁,...,Rₙ ∈ F.

**Corollary 6** V(i, F, n) ⊃ W(i, F, n) any i ∈ U F ∈ TAUT n ∈ ℕ.

**Definition 20** Y(i, F, n) for (Q₀ ⊃ F) ∧ Qₙ ∧ ⋀₁≤m≤n (Qₘ ⊃ Qₘ₋₁) any i ∈ U F ∈ TAUT n ∈ ℕ some single letters Q₀,...,Qₙ ∈ F.

**Corollary 7** W(i, F, n) ⊃ Y(i, F, n) any i ∈ U F ∈ TAUT n ∈ ℕ.

**Corollary 8** If ⊢ B → T(i, ¬F.∅, ∅.1) in p(F) then the truth values of Q₀,...,Qₙ, R₁,...,Rₙ in W(i, F, n), and Y(i, F, n), where n ≤ c·|F|^q, are computable in polynomial time n some c q ∈ ℕ any i ∈ U any sufficiently large F ∈ TAUT some n ∈ ℕ.

**Lemma 3** ⊢ B → T(i, ¬F.∅, ∅.1) in p(F) ⊃ Y(i, F, n) ∧ n ≤ c·|F|^q some c q ∈ ℕ any i ∈ U any sufficiently large F ∈ TAUT some n ∈ ℕ.

Proof:

```
⋆  ⊢ B → T(i, ¬F.∅, ∅.1) in p(F)  i ∈ U sufficiently large F ∈ TAUT       (41)
⋆  H(⊢ B → T(i, ¬F.∅, ∅.1), n) ∧ n ≤ c·|F|^q  some c q ∈ ℕ              (42)
⋆  Y(i, F, n), lemma 2 and corollaries 6-8                                  (43)
⊢ B → T(i, ¬F.∅, ∅.1) in p(F) ⊃ Y(i, F, n) ∧ n ≤ c·|F|^q                (44)
some c q ∈ ℕ any i ∈ U sufficiently large F ∈ TAUT some n ∈ ℕ
```

---

### 4.1 Proof complexity

**Definition 21** G(A₁,...,Aₘ ⊢ Fₙ, u) for A₁,...,Aₘ ⊢ Fₙ ∧ u = Σ₁≤k≤n |Fₖ|.

**Definition 22** A ⊢_R F for there is a deduction of a DNF formula F from a CNF formula A by resolution (including propositional logic).

**Definition 23** G(A ⊢_R F, u) for there is a resolution deduction of a DNF formula F from a CNF formula A and u is the number of symbols in the deduction, A F ∈ F.

**Definition 24** A ⊢_R F in p(F) for G(A ⊢_R F, u) ∧ u ≤ c·|F|^q some c q ∈ ℕ any A F ∈ F some u ∈ ℕ.

---

## Main Results

**Theorem 1** SAT ∉ P is true in a simply consistent extension B' of theory **B**.

Proof:

```
⋆  SAT ∈ P in a simply consistent extension B' of B, definition 15           (46)
⋆  ⊢ B → T(i, ¬F.∅, ∅.1) in p(F) some i ∈ U any F ∈ TAUT, corollary 5    (47)
⋆  ⊢ B → T(i, ¬PFₘ.∅, ∅.1) in p(PFₘ) any sufficiently large m             (48)
⋆  Y(i, PFₘ, n) ∧ n ≤ c·|PFₘ|^q some c q ∈ ℕ sufficiently large m, lemma 3 (49)
⋆  (Q₀ ⊃ PFₘ) ∧ Qₙ ∧ ⋀₁≤k≤n (Qₖ ⊃ Qₖ₋₁) some single letters Q₀,...,Qₙ ∈ F (50)
⋆  ⊢_R PFₘ in p(PFₘ) sufficiently large m, by (50) and (49)                 (51)
⋆  ¬(⊢_R PFₘ in p(PFₘ)) sufficiently large m, Haken's theorem, contradiction (52)
SAT ∉ P in a simply consistent extension B' of B, corollary 2               (53)
```

**Theorem 2** P ≠ NP is true in a simply consistent extension B'' of theory **B**.

(By the Cook-Levin theorem and theorem 1.)

**Corollary 9** SAT ∉ P is true, and provable in a simply consistent extension B' of theory **B**.

**Corollary 10** P ≠ NP is true, and provable in a simply consistent extension B'' of theory **B**.

---

## References

1. Miklos Ajtai. The complexity of the pigeonhole principle. In Proceedings of the 29th Annual IEEE Symposium on the Foundations of Computer Science, pages 346-355, 1988.
2. Paul Beame, Russell Impagliazzo, Jan Krajicek, Toniann Pitassi, Pavel Pudlak, and Alan Woods. Exponential lower bounds for the pigeonhole principle. STOC '92, pages 200-220, 1992.
3. Stephen Bellantoni, Toniann Pitassi, and Alasdair Urquhart. Approximation and Small-Depth Frege Proofs. SIAM Journal on Computing, 21(6):1161-1179, 1992.
4. Stephen Cook. The complexity of theorem-proving procedures. Third Annual ACM STOC, pages 151-158, 1971.
5. Stephen A. Cook. The Importance of the P versus NP Question. Journal of the ACM, 50(1):27-29, 2003.
6. Stephen A. Cook and Robert A. Reckhow. The relative efficiency of propositional proof systems. Journal of Symbolic Logic, 44(1):36-50, 1979.
7. Martin Davis. Computability and Unsolvability. McGraw-Hill, 1958.
8. Gerhard Gentzen. Untersuchungen uber das Logische Schliessen. Mathematische Zeitschrift, 39:176-210 and 405-431, 1935.
9. Armin Haken. The intractability of resolution (complexity). Theoretical Computer Science, 39:297-308, 1985.
10. J. Hartmanis and R. E. Stearns. On the computational complexity of algorithms. Transactions of the AMS, 117:285-306, 1965.
11. Jacques Herbrand. Recherches sur la theorie de la demonstration. Thesis, University of Paris, 1930.
12. David Hilbert and Paul Bernays. Grundlagen der Mathematik, volume 1. Springer-Verlag, 1934.
13. Richard M. Karp. Reducibility among combinatorial problems. In Complexity of Computer Computations, pages 85-103. Plenum Press, 1972.
14. Stephen C. Kleene. Mathematical Logic. John Wiley and Sons, 1967.
15. Jan Krajicek, Pavel Pudlak, and Alan Woods. An exponential lower bound to the size of bounded depth Frege proofs of the pigeonhole principle. Random Structures and Algorithms, 7(1):15-39, 1995.
16. L. Levin. Universal search problems (in Russian). Problemy Peredachi Informatsii, 9(3):115-116, 1973.
17. Marvin Minsky. Computation Finite and Infinite Machines. Prentice-Hall, 1967.
18. Toniann Pitassi, Paul Beame, and Russell Impagliazzo. Exponential lower bounds for the pigeonhole principle. Computational Complexity, 3(2):97-140, 1993.
19. Emil L. Post. Recursive Unsolvability of a Problem of Thue. Journal of Symbolic Logic, 12(3):1-11, 1947.
20. W. V. Quine. Methods of Logic, volume 3. Routledge & Keagan Paul, 1974.
21. John Alan Robinson. A Machine-Oriented Logic Based on the Resolution Principle. Journal of the ACM, 12(1):23-41, 1965.
22. Michael Sipser. Introduction to the Theory of Computation. Thomson Course Technology, 2005.
23. Steve Smale. Mathematical Problems for the Next Century. Mathematical Intelligencer, 20:7-15, 1998.
24. Sten-Ake Tarnlund. Computing. Updated 2008, Nov 2004.
25. Alan M. Turing. On Computable Numbers with an Application to the Entscheidungsproblem. Proceedings of the London Mathematical Society, 2/46:230-265, 1936.
