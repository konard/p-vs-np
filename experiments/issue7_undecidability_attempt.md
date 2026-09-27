# Experimental Investigation: P vs NP Independence (Issue #7)

**Created**: 2026-01-18
**Status**: Exploratory research, corrected in issue #579
**Goal**: Investigate whether P vs NP could be independent of ZFC

## Executive Summary

P = NP is an arithmetic statement. Standard set forcing preserves arithmetic
truth, so forcing a different answer over a fixed ground model cannot establish
its independence. This observation does **not** show that ZFC proves P = NP or
P ≠ NP. Independence from ZFC remains open. In particular, classical excluded
middle proves only `(P = NP) ∨ (P ≠ NP)`; it does not choose a branch.

The accompanying Lean files are illustrations of these logical distinctions.
They do not formalize the definition of P, NP, ZFC, forcing, or Shoenfield's
theorem.

## 1. Arithmetic Form of P = NP

By NP-completeness of SAT, P = NP is equivalent to the existence of a
deterministic polynomial-time SAT decider. Encode a Turing machine and a
polynomial clock by natural numbers `e` and `k`. A standard form is:

```text
P = NP  ⟺  ∃ e, k ∀ input x,
    [machine e halts within its polynomial clock on x
     and returns the correct SAT answer for x].
```

The clock bound and the machine simulation are finite computations. SAT of a
given input is decidable by finite exhaustive search. After fixing `e`, `k`,
and `x`, the bracketed relation is therefore computable. The displayed form
is Σ⁰₂ in the arithmetical hierarchy; its negation, P ≠ NP, is Π⁰₂. This is
an upper bound on syntactic complexity, not a claim of completeness at either
level. The quantifiers range over codes of finite machines and inputs, not
over arbitrary functions or languages as unanalyzed higher-order objects.

## 2. Absoluteness and Provability

Shoenfield absoluteness applies to projective Σ¹₂ and Π¹₂ formulas between
appropriate transitive models with the same ordinals. In particular, arithmetic
statements are absolute between a transitive ground model of set theory and
its set-forcing extensions. A forcing extension has the same natural numbers
and finite computations as its ground model, so it preserves the truth of
the clocked-SAT statement above.

This is a relation between **particular models**. Independence from a theory
is a statement about **proofs**: ZFC proves neither the sentence nor its
negation. If a sentence is independent, completeness gives models of ZFC on
both sides (assuming the relevant consistency). Those models need not form a
ground-model/forcing-extension pair. They may be nonstandard or otherwise
outside the hypotheses of the absoluteness argument. Thus forcing invariance
does not establish provability or refutability in ZFC.

For a focused discussion of this distinction, see [Aaronson, *P ?= NP*,
section 3.1 and footnote 24](https://www.scottaaronson.com/papers/pnp.pdf).

## 3. What the Forcing Attempt Shows

Consider a transitive model `M` of ZFC and a set-forcing extension `M[G]`.
Forcing preserves arithmetic truth in this setting, so:

```text
M ⊨ "P = NP"  ⟺  M[G] ⊨ "P = NP".
```

A generic set cannot become the code of a new finite Turing machine. A
procedure that queries the generic set is an oracle algorithm, and its
existence does not yield an ordinary polynomial-time SAT decider. The valid
conclusion is limited to the failure of this particular truth-changing
forcing plan. It does not rule out research on independence from ZFC, PA, or
bounded arithmetic.

Nonstandard models deserve separate treatment. A model of arithmetic can
have nonstandard natural numbers and machine codes. Truth of a Π⁰₂ or Σ⁰₂
sentence may differ between models of a theory; the standard model still has
a definite answer. A definite standard truth value alone gives no proof in
ZFC.

## 4. Comparison with the Continuum Hypothesis

CH is independent of ZFC (assuming ZFC is consistent), and forcing can change
its truth value. CH concerns cardinalities of sets of reals and is **not** an
ordinary projective Π¹₂ statement. Projective Σ¹₂/Π¹₂ statements are in the
scope of Shoenfield absoluteness, so labeling CH Π¹₂ would invert the
comparison. The difference here is that CH can change in set-forcing
extensions while arithmetic truth cannot.

## 5. Further Research Directions

- **Proof theory:** Ask whether PA, bounded arithmetic, or other specified
  theories prove one side. The arithmetical hierarchy alone does not answer
  this question. A true arithmetic sentence can be unprovable in a theory.
- **Model theory:** Formulate P = NP precisely in nonstandard models and
  identify which absoluteness hypotheses apply.
- **Complexity theory:** Seek a direct proof or an independence result with
  explicit axioms and a rigorous metatheorem. Relativization and other known
  barriers restrict techniques; they do not settle provability in ZFC.

There is no demonstrated theorem here that P vs NP is independent of a weak
theory, and no theorem that it is resolved by PA or ZFC. Those questions
remain open.

## 6. Scope of the Lean Experiments

`issue7_shoenfield_absoluteness.lean` proves excluded middle for a schematic
clocked-SAT proposition and shows that this is compatible with an abstract
independence predicate. The `correctClockedSAT` Boolean relation is a
placeholder; its connection to real Turing machines is not formalized.

`issue7_undecidability_formalization.lean` proves a conditional implication:
if two model interpretations have the same arithmetic truth, then P = NP has
the same truth value in both. Its arithmetic absoluteness premise is supplied
as a hypothesis. Neither Lean result proves a statement about ZFC
independence.

## 7. Assessment

The current result is a useful restriction on one family of forcing plans.
The likelihood of ZFC independence is a matter of expert judgment, not a
consequence of Shoenfield absoluteness. The precise provability status of
P = NP and P ≠ NP is unresolved.

## 8. References

1. Scott Aaronson, [*P ?= NP*, section 3.1](https://www.scottaaronson.com/papers/pnp.pdf).
2. J. R. Shoenfield, “The problem of predicativity” (1961).
3. Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach* (2009).
4. Jan Krajíček, *Bounded Arithmetic, Propositional Logic, and Complexity Theory* (1995).
