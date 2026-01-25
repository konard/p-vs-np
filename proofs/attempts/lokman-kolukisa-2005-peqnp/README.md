# Lokman Kolukisa (2005) - P=NP via Tautology Checking

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 22 (Woeginger's list)
- **Author**: Lokman Kolukisa
- **Year**: October 2005
- **Claim**: P=NP
- **Title**: "Two Dimensional Formulas and Tautology Checking"
- **Original Source**: http://geocities.com/lkoluk2003/ (defunct)
- **Status**: Refuted (error in algorithm)

## Summary

In October 2005, Lokman Kolukisa claimed to have designed a polynomial time algorithm for recognizing tautologies. Since tautology checking (TAUT) is co-NP-complete, a polynomial time algorithm would imply P=co-NP. Furthermore, since NP is closed under complement, this would also imply P=NP.

## Main Argument

The proof attempt follows this logical chain:

1. **Claim**: There exists a polynomial time algorithm for TAUT (tautology checking)
2. **Implication 1**: TAUT ∈ P → P=co-NP (since TAUT is co-NP-complete)
3. **Implication 2**: P=co-NP → P=NP (using closure properties)
4. **Conclusion**: P=NP

### The Proposed Approach

The paper proposes using "two-dimensional formulas" as a representation method for Boolean formulas, claiming this representation enables polynomial time tautology checking.

## Background: Why TAUT is co-NP-complete

### The Tautology Problem (TAUT)

**Definition**: Given a Boolean formula φ, determine whether φ is a tautology (i.e., true for all possible assignments of its variables).

**Complexity**:
- TAUT is in co-NP because a non-tautology can be verified in polynomial time by providing a falsifying assignment
- TAUT is co-NP-complete (complement of SAT, which is NP-complete)

### Why P=co-NP implies P=NP

If P=co-NP, then for every problem L in NP:
1. The complement L̄ is in co-NP
2. Since P=co-NP, we have L̄ ∈ P
3. Since P is closed under complement, L ∈ P
4. Therefore, NP ⊆ P
5. Combined with P ⊆ NP (trivial), we get P=NP

## The Error in the Proof

The fundamental error in this proof attempt is the **claim that tautology checking can be done in polynomial time** using two-dimensional formulas.

### Why the Algorithm Cannot Work

1. **Representation Cannot Reduce Complexity**: Changing the representation of a formula (from CNF/DNF to "two-dimensional") does not fundamentally change the computational complexity of the decision problem. The problem remains co-NP-complete regardless of representation.

2. **Missing Verification**: The paper does not provide:
   - A rigorous proof that the algorithm correctly decides all tautologies
   - A rigorous analysis showing the algorithm runs in polynomial time
   - Treatment of all possible formula structures

3. **Circular Reasoning**: Any algorithm that claims to solve TAUT in polynomial time must handle all possible Boolean formulas. The "two-dimensional" representation, if it simplifies some cases, must either:
   - Take exponential time to convert arbitrary formulas to this representation, OR
   - Fail to represent some formulas correctly, OR
   - Still require exponential time to check tautologies in this representation

### Formal Gap

The critical gap is between:
- **Claimed**: Algorithm A decides TAUT in polynomial time
- **Required**: Proof that ∀φ. (A(φ) = true ↔ φ is a tautology) ∧ (time(A, φ) ≤ p(|φ|)) for some polynomial p

This gap cannot be bridged without violating known complexity-theoretic barriers, assuming P≠NP.

## Formalization Structure

This directory contains formal specifications that:

1. **Define the tautology problem** (TAUT) and its co-NP-completeness
2. **Formalize the claim** that TAUT ∈ P
3. **Prove the implications**: TAUT ∈ P → P=co-NP → P=NP
4. **Identify the gap**: Show that the algorithm cannot be proven correct without additional assumptions

### Files

- `rocq/KolukisaAttempt.v` - Rocq formalization
- `lean/KolukisaAttempt.lean` - Lean 4 formalization
- `isabelle/KolukisaAttempt.thy` - Isabelle/HOL formalization

## Key Insights

1. **The logic is sound**: IF there were a polynomial time algorithm for TAUT, THEN P=NP would follow
2. **The algorithm is unsound**: The claimed polynomial time algorithm for TAUT does not work
3. **Representation vs. Complexity**: Changing how formulas are represented does not change the fundamental computational complexity

## References

### Primary Source
- **Kolukisa, L.** (2005). "Two Dimensional Formulas and Tautology Checking" (unpublished/defunct)

### Woeginger's List
- **Woeginger, G.J.** "The P-versus-NP page" - Entry #22
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Background on co-NP and TAUT
- **Cook, S.** (1971). "The complexity of theorem-proving procedures." *STOC*
- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach* - Chapter 2
- **Sipser, M.** (2012). *Introduction to the Theory of Computation* - Chapter 7.4

### Complexity Class Relationships
- **Stockmeyer, L.** (1976). "The polynomial-time hierarchy." *Theoretical Computer Science*

## Learning Value

This attempt demonstrates:

1. **Common pitfall**: Confusing representation with computational complexity
2. **Importance of rigor**: Claims of polynomial algorithms must include complete correctness proofs
3. **Verification burden**: Showing an algorithm is correct requires handling all possible inputs
4. **Complexity barriers**: Some problems are provably hard (assuming standard complexity assumptions)

## Formal Verification Status

- ✅ Rocq: Definitions and implications formalized
- ✅ Lean: Definitions and implications formalized
- ✅ Isabelle: Definitions and implications formalized
- ⚠️ Gap identified: Algorithm correctness cannot be proven

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #112](https://github.com/konard/p-vs-np/issues/112) | [Pull Request #394](https://github.com/konard/p-vs-np/pull/394)
