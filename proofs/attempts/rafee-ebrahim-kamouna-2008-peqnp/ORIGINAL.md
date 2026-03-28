# The Kleene-Rosser Paradox, The Liar's Paradox & A Fuzzy Logic Programming Paradox Imply SAT is (NOT) NP-complete

**Author**: Rafee Ebrahim Kamouna
**Email**: rafee102000@yahoo.com
**ArXiv**: [0806.2947v8 [cs.LO]](https://arxiv.org/abs/0806.2947)
**Date**: 10 Jul 2009
**Submitted to**: ACM Transactions on Computation Theory

> What is a Turing machine?
> Impetuous Fire,
> Syntactico-Semantical!
> Ice and Desire,
> Computation wags on...
> [Turing à la "Romeo & Juliet"]

## Abstract

After examining the P versus NP problem against the Kleene-Rosser paradox of the λ-calculus, it was found that it represents a counter-example to NP-completeness. We prove that it contradicts the proof of Cook's theorem. A logical formalization of the liar's paradox leads to the same result. This formalization of the liar's paradox into a computable form is a 2-valued instance of a fuzzy logic programming paradox. Three proofs that show that SAT is (NOT) NP-complete are presented. The counter-example classes to NP-completeness are also counter-examples to Fagin's theorem and the Immermann-Vardi theorem, the fundamental results of descriptive complexity. All these results show that ZFC is inconsistent.

## Note

This is a markdown summary of the original paper. The full PDF is available in `ORIGINAL.pdf` or at https://arxiv.org/pdf/0806.2947.pdf

**The paper's claims have been refuted by the complexity theory community.** See `README.md` and `refutation/` folder for detailed analysis and formal refutations of the errors in this attempt.

## Main Content Summary

The paper presents three main "theorems" claiming to prove P = NP by showing SAT is not NP-complete:

### 1. Introduction and the Kleene-Rosser Paradox

The author examines the Kleene-Rosser paradox from λ-calculus:
- Defines `k = (λx.¬(xx))`
- Claims `kk = ¬(kk)` represents a paradoxical language
- Argues this paradoxical language cannot be reduced to SAT
- Concludes SAT is not NP-complete

**Error**: Confuses logical paradoxes (meta-level) with computational problems (object-level).

### 2. Theorem 1.1: Main Theorem - SAT is NOT NP-complete

Claims that if we have a paradox recognizer `Mλ` that accepts paradoxical strings, then the corresponding SAT formula φ would be paradoxical, which is impossible.

**Error**: SAT formulas are not paradoxical - they either have satisfying assignments or they don't. Category mistake.

### 3. Theorem 1.2: Alternative Proof

Claims that paradoxical strings (simultaneously true and false) cannot be converted to SAT instances (which are either true or false).

**Error**: Fails to understand that SAT asks "does there exist an assignment?" not "is this string true?". More category confusion.

### 4. Theorem 1.3: P = NP

Concludes that if SAT is not NP-complete, then the set of NP-complete problems is empty, therefore P = NP.

**Error**: The conclusion would only follow if the premises were valid, which they are not.

### 5. Extended Claims

The paper also claims these results show:
- ZFC set theory is inconsistent
- Fagin's theorem is refuted
- Immermann-Vardi theorem is refuted
- Various other fundamental results are wrong

**Error**: Extraordinary claims without rigorous proof. The category errors in the foundational arguments invalidate all derivative claims.

## Critical Reception

The paper was never peer-reviewed and appears only on arXiv. The computational complexity community has widely rejected it as based on fundamental misunderstandings:

1. **Category confusion**: Treating logical paradoxes as computational problems
2. **Misunderstanding Cook's Theorem**: Not engaging with the actual proof structure
3. **Lack of formalism**: Using informal analogies instead of rigorous mathematics
4. **Implausible conclusions**: Jumping from complexity theory to ZFC inconsistency

For a detailed refutation, see the `refutation/` folder in this directory.
