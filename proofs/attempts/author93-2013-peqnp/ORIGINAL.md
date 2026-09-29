# Linear Programming Formulation of Boolean Satisfiability Problem

**Author:** Algirdas Antano Maknickas
**Affiliation:** Vilnius Gediminas Technical University, Vilnius, Lithuania
**Year:** 2013 (published December 1, 2013)
**Conference:** International Conference on Advances in Engineering Technologies and Physical Science, Hong Kong
**Publisher:** Springer Science (Lecture Notes in Electrical Engineering, Vol. 275)
**DOI:** 10.1007/978-94-007-7684-5_22
**Claim:** P = NP (SAT can be solved in polynomial time via linear programming)

---

## Note on Availability

The original paper is behind a Springer paywall. This document is a reconstruction
of the paper's content based on available information from the publisher metadata,
references, and related literature.

---

## Abstract (Reconstructed)

The paper proposes a method for formulating the Boolean Satisfiability Problem (SAT)
as a Linear Programming (LP) problem. The author uses "new analytic multi-valued logic
expressions" to encode logical formulas as linear constraints. The paper first addresses
2SAT, then extends the approach to 3SAT and general kSAT, claiming that kSAT can be
solved in polynomial time using standard LP algorithms (e.g., interior point methods).
If correct, this would imply P = NP.

---

## The Approach (Reconstructed from Available Information)

### Step 1: Multi-valued Logic Formulation

The paper employs analytical expressions from multi-valued logic to represent Boolean
formulas. Boolean variables x_i take values in {0, 1}, which are embedded into a
continuous real-valued setting.

### Step 2: 2SAT as Linear Programming

The approach begins with 2SAT (satisfiability of conjunctions of clauses with at most
2 literals each). For a clause (l_1 ∨ l_2) where l_i are literals:

- Positive literal: x_i ≥ 0 and x_i ≤ 1
- Negated literal: (1 - x_i) used in place of ¬x_i

A clause (x_i ∨ x_j) is encoded as: x_i + x_j ≥ 1
A clause (¬x_i ∨ x_j) is encoded as: (1 - x_i) + x_j ≥ 1
A clause (x_i ∨ ¬x_j) is encoded as: x_i + (1 - x_j) ≥ 1
A clause (¬x_i ∨ ¬x_j) is encoded as: (1 - x_i) + (1 - x_j) ≥ 1

The SAT problem then becomes: find x_i ∈ [0,1] satisfying all such constraints.

### Step 3: Extension to kSAT

The same approach is extended to clauses with k literals. For a clause
(l_1 ∨ l_2 ∨ ... ∨ l_k), the LP constraint is:

    l'_1 + l'_2 + ... + l'_k ≥ 1

where l'_i = x_i if l_i is positive, and l'_i = (1 - x_i) if l_i is negative.

### Step 4: Polynomial-time Solution

The resulting LP can be solved in polynomial time using standard algorithms such as:
- Interior point methods (Khachiyan 1979, Karmarkar 1984)
- Simplex method

### Step 5: Conclusion

Since SAT is NP-complete and the LP formulation can be solved in polynomial time,
the author claims that SAT ∈ P, and therefore P = NP.

---

## The Claimed Main Theorem (Paraphrased)

**Theorem:** For any kSAT instance φ with n variables and m clauses, the LP:

    minimize 0
    subject to: Σ_{i in C} l'_i ≥ 1  for each clause C
                0 ≤ x_i ≤ 1           for each variable x_i

has a feasible solution if and only if φ is satisfiable.

---

## References from the Paper (as cited in Springer metadata)

1. Cook, S.A. (1971). The complexity of theorem-proving procedures. STOC 1971.
2. Karp, R.M. (1972). Reducibility among combinatorial problems.
3. Khachiyan, L.G. (1979). A polynomial algorithm in linear programming. Soviet Mathematics Doklady.
4. Karmarkar, N. (1984). A new polynomial-time algorithm for linear programming. Combinatorica.
5. Maknickas, A.A. (2013). Linear Programming Formulation of Boolean Satisfiability Problem.
   In: Transactions on Engineering Technologies. Lecture Notes in Electrical Engineering, vol 275. Springer.
