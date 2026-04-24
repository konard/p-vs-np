# Original Paper: Topological Approach to Solve P Versus NP

**Author:** Koji Kobayashi
**Year:** 2012 (submitted February 6, 2012)
**arXiv ID:** [arXiv:1202.1194](https://arxiv.org/abs/1202.1194)
**Woeginger's List:** Entry #78
**Language:** Japanese with English abstract

---

## Abstract (translated to English)

We prove P≠NP using a topological approach based on the resolution principle in propositional logic. We define several classes of CNF formulas — RCNF (Resolution CNF), TCNF (Triangular CNF), and CCNF (Chaotic CNF) — and show that CNF cannot be polynomially reduced to RCNF (which is P-complete), thereby establishing the separation P≠NP.

---

## Section 1: Introduction and Background

The paper begins by reviewing basic concepts from propositional logic:

- **Variables**: Boolean variables x₁, x₂, ..., xₙ
- **Literals**: Variables or their negations: x, ¬x
- **Clauses**: Disjunctions of literals: (x₁ ∨ ¬x₂ ∨ x₃)
- **CNF (Conjunctive Normal Form)**: Conjunction of clauses
- **HornCNF**: CNF where each clause has at most one positive literal

The resolution principle is reviewed:

**Resolution Rule**: From clause C₁ = (A ∨ x) and C₂ = (B ∨ ¬x), derive the resolvent C = (A ∨ B)

Here x is called the "joint variable," C₁ and C₂ are "antecedents," and C is the "consequent."

---

## Section 2: Resolution Structure Theorems

### Theorem 3 (Resolution Connectivity)
Antecedents of a resolution connect to each other via exactly one joint variable.

### Theorem 4 (Consequent as Linkage)
The consequent becomes a linkage of antecedents — removing one literal from each antecedent and joining the remainders.

### Theorem 5 (Proof Structure)
A resolution proof forms a directed acyclic graph where each node is either an axiom (original clause) or derived by resolution.

### Theorem 6 (Clauses Product)
The consequent is the "clauses product" of its positive and negative antecedents, representing a product structure in the resolution DAG.

---

## Section 3: RCNF — Resolution CNF (Definition 9)

RCNF encodes the resolution structure of a formula as a new formula:
- Each clause of the original formula becomes a variable in RCNF
- Each resolution step becomes a clause in RCNF
- Antecedents become negative literals, consequents become positive literals

**Formal Definition**: Given CNF formula F with clauses C₁, ..., Cₘ, the RCNF is:
```
RCNF(F) = {¬c_i₁ ∨ ... ∨ ¬c_iₖ ∨ c_j : C_j is resolvent of C_i₁,...,C_iₖ}
```

This construction always produces a HornCNF formula.

### Theorem 10 (RCNF is P-Complete)
RCNF is P-complete:
1. HornCNF reduces to RCNF in logarithmic space
2. Deciding satisfiability of RCNF is in P

The proof shows a log-space reduction from HornCNF to RCNF, establishing P-completeness.

---

## Section 4: TCNF — Triangular CNF (Definition 13)

For three propositional variables P, Q, R, define:
```
T_PQR = c_PQ ∧ c_QR ∧ c_PR ∧ c_PQR
```

where:
- c_PQ = (¬P ∨ ¬Q) — "P and Q cannot both be true"
- c_QR = (¬Q ∨ ¬R)
- c_PR = (¬P ∨ ¬R)
- c_PQR = (¬P ∨ ¬Q ∨ R) — "if P and Q, then R"

The paper claims T_PQR represents a triangular structure related to a Moore graph.

### Theorem 14 (TCNF is NP-Complete)
TCNF is NP-complete via polynomial-time reduction from 3CNF to TCNF.

### Theorem 15 (TCNF is Product Irreducible)
T_PQR cannot be factored as a direct product of smaller formulas.
This "irreducibility" is central to the paper's argument that TCNF cannot be represented compactly in RCNF.

---

## Section 5: CCNF — Chaotic CNF (Definition 16)

CCNF combines multiple TCNFs using a Moore graph structure:

**Definition**: Given a Moore graph G with diameter k and degree 3:
- Each node of G corresponds to a TCNF T_PᵢQᵢRᵢ
- Each edge of G corresponds to a shared variable between adjacent TCNFs
- The resulting formula M_k is a conjunction of all the TCNFs

**Moore Graphs**: A Moore graph with diameter k and degree d has the maximum possible number of vertices given these constraints. For diameter 2, degree 3, there is only the Petersen graph (10 vertices).

### Theorem 17 (Existence of Chaotic MUC)
For every k, there exists M_k ∈ CMUC (Chaotic Minimal Unsatisfiable Core).

The paper uses the existence of Moore graphs of every diameter to construct formulas M_k with increasing "chaos."

---

## Section 6: The Main Separation Argument

### Theorem 18 (Falsifying Assignment Size)
For F ∈ CMUC, the number of falsifying assignments |[b[c]]| is not polynomial in |F|.

The argument: the CCNF formulas M_k have a Moore graph structure, and the number of falsifying assignments grows super-polynomially due to the high connectivity and "irreducibility" of the structure.

### Theorem 19 (RCNF Requires Super-Polynomial Size)
For some F ∈ CNF:
```
O(RCNF(F)) > O(|F|^m)  for every constant m
```

The argument: M_k (CCNF formulas) cannot be efficiently represented in RCNF because the "chaotic" structure of M_k cannot be captured by the Horn-style structure of RCNF without exponential blowup.

### Theorem 20 (Main Result: P ≠ NP)
Since:
1. RCNF ≡_L HornCNF (RCNF is P-complete, equivalent to HornCNF in log-space)
2. Some CNF formulas cannot be polynomially reduced to RCNF (Theorem 19)

Therefore: CNF ⊈_p RCNF ≡_L HornCNF

Since HornCNF is P-complete and CNF (i.e., SAT) cannot be reduced to it polynomially, the paper concludes P ≠ NP.

---

## Section 7: Conclusion

The paper concludes by claiming that:
1. The topological structure of resolution (RCNF) represents the P-complete class
2. Chaotic CNF formulas (based on Moore graphs) cannot be represented compactly in RCNF
3. Therefore SAT ∉ P, i.e., P ≠ NP

---

## Key Definitions Summary

| Term | Symbol | Meaning |
|------|--------|---------|
| Resolution CNF | RCNF | HornCNF encoding resolution structure |
| Triangular CNF | TCNF | Triangle-structured formula T_PQR |
| Chaotic CNF | CCNF | Moore-graph combination of TCNFs |
| Chaotic MUC | CMUC | Minimal Unsatisfiable Core that is "chaotic" |
| Product Reducible | — | Formula expressible as direct product |
| Clauses Product | — | The structure of resolution consequents |

---

## References in the Paper

1. Sipser, M. "Introduction to the Theory of Computation" (Japanese translation)
2. Kobayashi, K. (2012). arXiv:1202.1194
