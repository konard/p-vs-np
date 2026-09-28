# Koji Kobayashi (2012): P ≠ NP via Topological Approach

**Attempt ID**: 78
**Author**: Koji Kobayashi
**Year**: 2012
**Claim**: P ≠ NP
**ArXiv**: [arXiv:1202.1194](https://arxiv.org/abs/1202.1194)
**Woeginger's List**: Entry #78

## Summary

In February 2012, Koji Kobayashi published a paper titled "Topological approach to solve P versus NP" claiming to prove that P ≠ NP. The approach uses a framework based on the resolution principle in propositional logic, defining new classes of CNF formulas (RCNF, TCNF, CCNF) and arguing that some CNF formulas cannot be polynomially reduced to a P-complete class (RCNF), thereby claiming to establish P ≠ NP.

## Main Argument

Kobayashi's proof strategy follows this structure:

### 1. Resolution Principle Analysis

The paper analyzes resolution in propositional logic:
- **Theorem 3**: Antecedents of a resolution share exactly one joint variable
- **Theorem 4**: Consequent becomes a linkage of antecedents
- **Theorem 6**: Consequent is the "clauses product" of antecedents

### 2. RCNF (Resolution CNF) — A P-Complete Class

**Definition 9**: RCNF encodes the resolution structure of a formula as a HornCNF:
- Original clauses become variables in RCNF
- Resolution steps become Horn clauses (antecedents negative, consequent positive)

**Theorem 10**: RCNF is P-Complete via log-space reduction from HornCNF

### 3. TCNF (Triangular CNF) — An NP-Complete Class

**Definition 13**: For variables P, Q, R:
```
T_PQR = (¬P ∨ ¬Q) ∧ (¬Q ∨ ¬R) ∧ (¬P ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ R)
```

**Theorem 14**: TCNF is NP-Complete via polynomial reduction from 3CNF

**Theorem 15**: TCNF is "product irreducible" — T_PQR cannot be factored

### 4. CCNF (Chaotic CNF) — The Separation

**Definition 16**: CCNF combines TCNFs using a Moore graph structure:
- Nodes = TCNF formulas, Edges = shared variables between adjacent TCNFs
- Diameter k, degree 3

**Theorem 17**: Chaotic MUC formulas M_k exist for all k

**Theorem 18**: For F ∈ CMUC, the number of falsifying assignments is super-polynomial

**Theorem 19**: Some CNF formulas require super-polynomial RCNF size

**Theorem 20**: CNF ⊈_p RCNF ≡_L HornCNF, claimed to imply P ≠ NP

## The Error in the Proof

### Critical Gap: Representation Complexity ≠ Computational Complexity

The fundamental error is in the final step (Theorem 20):

**Kobayashi argues**:
1. RCNF is P-complete (correct)
2. Some CNF formulas cannot be polynomially reduced to RCNF (claimed in Theorem 19)
3. Therefore P ≠ NP (INCORRECT CONCLUSION)

**Why this is wrong**:

The fact that CNF formulas cannot be compactly represented in RCNF does **not** imply that SAT cannot be decided in polynomial time. P vs NP is about whether satisfiability can be decided by **any** polynomial-time algorithm, not whether **one specific representation approach** (RCNF) works in polynomial size.

### Additional Issues

1. **Theorem 19 is unproven**: The paper claims CCNF formulas require super-polynomial RCNF but provides no proof connecting Theorem 18 (falsifying assignments) to RCNF size.

2. **Product irreducibility is undefined**: The notion of "product reducibility" (Definition 8) is not precisely defined, making Theorem 15 unverifiable.

3. **Theorem 17 is unproven**: The existence of Chaotic MUC formulas for all k is asserted without construction.

### The Analogy

- It is known that some integers require large unary representations
- This does not mean arithmetic is hard — other representations (binary) are efficient
- Similarly: CNF requiring large RCNF doesn't mean SAT is hard — other algorithms exist

## File Structure

```
proofs/attempts/koji-kobayashi-2012-pneqnp/
├── README.md                              # This file
├── original/
│   ├── README.md                          # Description of original paper
│   ├── ORIGINAL.md                        # Markdown conversion of the paper (English)
│   └── ORIGINAL.pdf                       # Original paper
├── proof/
│   ├── README.md                          # Explanation of forward proof formalization
│   ├── lean/
│   │   └── KobayashiProof.lean            # Lean 4 forward proof formalization
│   └── rocq/
│       └── KobayashiProof.v               # Rocq forward proof formalization
└── refutation/
    ├── README.md                          # Explanation of why the proof fails
    ├── lean/
    │   └── KobayashiRefutation.lean       # Lean 4 refutation formalization
    └── rocq/
        └── KobayashiRefutation.v          # Rocq refutation formalization
```

## Formalization Status

- **Paper analyzed**: ✅
- **Error identified**: ✅ (Representation complexity ≠ decision complexity)
- **Original markdown**: ✅
- **Proof formalization (Lean)**: ✅ (with `sorry` at unjustified steps)
- **Proof formalization (Rocq)**: ✅ (with `Admitted` at unjustified steps)
- **Refutation (Lean)**: ✅
- **Refutation (Rocq)**: ✅

## References

1. Kobayashi, K. (2012). "Topological approach to solve P versus NP". arXiv:1202.1194
2. Woeginger, G. J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Haken, A. (1985). "The intractability of resolution". Theoretical Computer Science, 39, 297–308.

---

**Navigation**: [Main README](../../../README.md) | [All Attempts](../ATTEMPTS.md)
