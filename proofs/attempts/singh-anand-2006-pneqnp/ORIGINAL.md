# An Elementary Proof That P ≠ NP

**Author**: Bhupinder Singh Anand
**Year**: 2006 (revised February 2007)
**arXiv ID**: [math.GM/0603605](http://arxiv.org/abs/math.GM/0603605)
**Woeginger's List**: Entry #27

---

## Note

This is a markdown reconstruction of the paper's argument based on the arXiv abstract and the mathematical content described in available reviews. The original paper is available at [arXiv:math/0603605](http://arxiv.org/abs/math.GM/0603605).

---

## Abstract (Reconstructed)

The paper claims to prove P ≠ NP via an argument about non-standard models of Peano Arithmetic (PA). The central claim is:

1. If PA has no non-standard models, then P ≠ NP.
2. PA has no non-standard models (claimed proof via induction).
3. Therefore, P ≠ NP.

---

## Main Argument

### Gödelian Background

The paper begins by referencing Gödel's famous undecidable formula R(x) in PA, which is:

- **Turing-decidable** (for any given natural number n, we can verify whether R(n) holds)
- **Not PA-provable** (there is no PA proof of R(x) for all x)

The author introduces the terminology:

> "An arithmetical tautology is *Turing-decidable* if it can be verified as true for any given standard natural number by a Turing machine."

### Connection to PA Models

The paper then claims:

1. If every Turing-computable arithmetical tautology is PA-provable, then R(x) cannot be Turing-computable (a contradiction with its known properties).
2. Therefore, if PA has no non-standard models, then there must exist Turing-decidable tautologies that are not PA-provable.
3. This gap—Turing-decidable but not PA-provable—would separate the "verification" class (NP) from the "decision" class (P).

Formally the paper states:

> "If the interpretation of PA over the standard model is the only model of PA, then every Turing-decidable arithmetical tautology must be PA-provable."

### Proving PA Has No Non-Standard Models

The paper's key step is a claimed proof that PA has no non-standard models, proceeding as follows:

**Definition of formula G(x):**
```
G(x) := [x = 0 ∨ ¬(∀y)¬(x = y')]
```
This formula says: "x is 0, or x is the successor of some y."

**Induction argument:**

- **Base case**: G(0) is provable in PA (since x = 0 is satisfied directly).
- **Inductive step**: G(x) → G(x') is provable in PA (since x' is the successor of x, so x' satisfies the successor clause).
- **By the induction axiom of PA**: (∀x)G(x) is provable in PA.

**The claimed conclusion:**

The author asserts that since (∀x)G(x) is provable in PA, every element of every model of PA must be 0 or a successor of a natural number. Therefore, the author claims, there cannot be any non-standard elements—PA has no non-standard models.

### Claimed Result: P ≠ NP

Combining the two steps:

1. PA has no non-standard models (claimed above).
2. If PA has no non-standard models, then not every Turing-decidable tautology is PA-provable.
3. This separation yields P ≠ NP.

---

## Key Mathematical Objects

### The Formula G(x)

```
G(x) := (x = 0) ∨ (∃y)(x = S(y))
```

Where S is the successor function. This says: every element is either zero or a successor.

### The Induction Schema of PA

For any formula φ(x):
```
[φ(0) ∧ (∀x)(φ(x) → φ(S(x)))] → (∀x)φ(x)
```

### Application

The paper applies the induction schema to G(x):
```
G(0) ∧ (∀x)(G(x) → G(S(x))) → (∀x)G(x)
```

Both premises are PA-provable, so (∀x)G(x) is PA-provable.

---

## The Author's Inference

The paper concludes that (∀x)G(x) being provable in PA means:

> "Every element of every model of PA is either 0 or the successor of another element. Since there are no elements that are infinitely far from 0, PA has no non-standard models."

---

## References Cited in the Paper

- **Mendelson, E.** (1964). *Introduction to Mathematical Logic*. Van Nostrand.
- **Gödel, K.** (1931). "On formally undecidable propositions of Principia Mathematica and related systems I."
- **Kleene, S.C.** (1952). *Introduction to Metamathematics*. North-Holland.

---

## Known Refutation

The proof fails at the key inference step. The formula (∀x)G(x) is indeed provable in PA, and by Gödel's Completeness Theorem it holds in **all** models of PA—including non-standard models. In non-standard models, the non-standard elements are each successors of other non-standard elements (forming infinite descending chains), so they all satisfy G(x). The formula does not eliminate non-standard models; it holds in them.

Gödel's Incompleteness Theorem, together with the Löwenheim-Skolem Theorem, actually **guarantees** that first-order PA has non-standard models. The author's inference from "(∀x)G(x) is provable" to "PA has no non-standard models" is the fundamental error.
