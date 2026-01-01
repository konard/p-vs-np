# Luiz Barbosa (2009) - P≠NP Attempt

**Attempt ID**: 51
**Author**: André Luiz Barbosa
**Year**: 2009
**Claim**: P≠NP
**Status**: **Refuted**

## Summary

In July 2009, André Luiz Barbosa published a paper claiming to prove P≠NP by constructing an artificial problem called XG-SAT (Extended General Problem of Satisfiability) and arguing that it is in NP but not in P. The paper proposes generalizations to the traditional definitions of P and NP.

## Main Argument

Barbosa's approach consists of:

1. **Definition of Restricted Type X Program**: Programs that accept n-bit inputs and run in polynomial time P(n) where P(n) is fixed for each program but not uniform across all programs.

2. **Definition of XG-SAT**: Given a restricted type X program S and input length n (in unary), determine whether S returns 1 for at least one input of length n.

3. **Generalization of P and NP**: Barbosa introduces "Lz-languages" (essentially promise problems) where the domain is restricted to some subset Lz ⊆ Σ*.

4. **Claim**: XG-SAT is in NP but not in P under these generalized definitions.

## The Refutation

In June 2011, Lane Hemaspaandra, Kyle Murray, and Xiaoqing Tang published a detailed refutation ([arXiv:1106.1150](https://arxiv.org/abs/1106.1150)) identifying two critical flaws:

### Error 1: Uniformity Problem

**The main technical error**: Barbosa's proof that XG-SAT ∈ NP fails due to a **uniformity problem**.

In Definition 2.1, Barbosa requires each restricted type X program to run in polynomial time P(n), but **crucially, there is no single shared polynomial** across all programs, and Barbosa explicitly avoids padding inputs with time bounds.

The problem:
- Different programs run in different polynomial times: linear, quadratic, cubic, etc.
- XG-SAT has **no obvious single polynomial** that upper-bounds the nondeterministic running time
- For a problem to be in NP, there must exist a **single polynomial** bounding the verification time
- Barbosa's construction has a different polynomial for each program, making it unclear that XG-SAT satisfies the standard NP definition

As Hemaspaandra et al. state: "Some machines will run in linear time, some will run in quadratic time, some in cubic time, and so on, and so the set XG-SAT has no obvious single polynomial upper-bounding the nondeterministic running time of a NTM accepting it."

### Error 2: Logical Implication

Even if Barbosa's generalized definitions were correct, **proving his version of P≠NP would automatically prove the standard P≠NP**.

Barbosa's claim is essentially: ∃Lz ⊆ Σ* such that P[Lz] ≠ NP[Lz]

However, as Hemaspaandra et al. prove:
- If P = NP in the standard sense, then for any Lz, we have P[Lz] = NP[Lz]
- By contrapositive: If P[Lz] ≠ NP[Lz] for some Lz, then P ≠ NP (standard)
- **Therefore**: Proving Barbosa's claim would solve the million-dollar Clay Institute problem

This makes it "exceedingly unlikely that Barbosa's proof can be fixed any time soon."

## Key Insights

### What Barbosa Actually Attempted

Barbosa redefined P and NP to work with promise problems (Lz-languages), essentially claiming:

> "There exists a promise problem that has a solution in NP but not in P"

This is **fundamentally different** from the standard P vs NP question.

### Why the Generalization Doesn't Help

1. **Non-uniform polynomials**: Allowing different polynomial bounds for different inputs breaks the uniformity required for complexity class membership

2. **Promise problems are stronger**: If you can separate P and NP even on a restricted domain with promises, you've solved the general problem

3. **Rice's Theorem barriers**: Many of Barbosa's diagonalization arguments run into undecidability issues from Rice's Theorem

## Related Concepts

- **Promise Problems**: Computational problems where inputs are restricted to come from a specific subset
- **Uniformity in Complexity**: The requirement that polynomial time bounds be uniform across all inputs
- **Rice's Theorem**: Properties of program behavior are generally undecidable
- **Diagonalization**: Proof technique used extensively by Barbosa

## Sources

- **Original Paper**: Barbosa, A. L. "P ≠ NP Proof" (2009)
  - arXiv: [0907.3965](https://arxiv.org/abs/0907.3965)
  - Note: Paper went through 38+ revisions

- **Refutation**: Hemaspaandra, L. A., Murray, K., & Tang, X. "Barbosa, Uniform Polynomial Time Bounds, and Promises" (2011)
  - arXiv: [1106.1150](https://arxiv.org/abs/1106.1150)

- **Woeginger's List**: Entry #51 at [https://wscor.win.tue.nl/woeginger/P-versus-NP.htm](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## Formalization Strategy

Our formalization focuses on:

1. **Modeling the core definitions**: Restricted type X programs, XG-SAT, Lz-languages
2. **Formalizing the uniformity gap**: Showing why multiple polynomial bounds prevent NP membership
3. **Demonstrating the logical implication**: If Barbosa's claim held, standard P≠NP would follow
4. **Exploring the undecidability issues**: Rice's Theorem obstacles to the proof strategy

The goal is to make the errors explicit and machine-checkable, serving as an educational resource about uniformity requirements in complexity theory.
