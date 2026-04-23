# Refutation: Vega Delgado 2010

This directory contains formal refutations of the core claims in Vega Delgado's November 2010 P ≠ NP proof attempt.

## Contents

- `lean/VegaDelgado2010Refutation.lean` - Lean 4 refutation
- `rocq/VegaDelgado2010Refutation.v` - Rocq refutation

## Why the Proof Fails

Vega Delgado's 2010 proof attempt is fundamentally circular.

---

## The Central Error: Circular Reasoning

### Background

The proof strategy is:
1. Construct a candidate one-way function `f`
2. Show `f` is hard to invert (the failing step)
3. Conclude one-way functions exist
4. Apply known theorem: one-way functions exist → P ≠ NP

Steps 3 and 4 are logically correct. The proof collapses at step 2.

### Why Step 2 Fails: Circular Dependence

**One-way functions and P vs NP are equivalent.**

The known relationships are:
- `one-way functions exist → P ≠ NP` (one direction is established)
- `P = NP → one-way functions do not exist` (the contrapositive is established)
- Whether `P ≠ NP → one-way functions exist` is itself an open problem

Therefore:
- To prove that a candidate function `f` is hard to invert, one must show that no polynomial-time algorithm can find preimages.
- But "no polynomial-time algorithm can do X" is precisely the kind of statement equivalent to P ≠ NP claims.
- Any rigorous proof of hardness of inversion would constitute, by itself, a proof of P ≠ NP — making the one-way function route redundant.

**Vega Delgado's proof provides no rigorous argument for hardness of inversion.** The informal argument used in the paper does not constitute a mathematical proof and, upon examination, either implicitly assumes what it tries to prove or makes claims that cannot be substantiated without first establishing P ≠ NP.

---

## Formal Statement of the Problem

The circularity can be stated precisely:

```
Goal: Prove P ≠ NP

Strategy:
  Lemma A: f is hard to invert
  Theorem: One-way functions exist (from Lemma A)
  Theorem: P ≠ NP (from "one-way functions exist → P ≠ NP")

Problem:
  Proof of Lemma A requires: "no poly-time algorithm inverts f"
  This is equivalent to: P ≠ NP (in terms of what needs to be shown)
  Therefore: the strategy is circular
```

---

## What Is Actually Needed

To non-circularly prove P ≠ NP via one-way functions, one would need a proof of hardness of inversion that:
1. Does not assume P ≠ NP (directly or indirectly)
2. Uses a fundamentally different technique (e.g., circuit complexity lower bounds, algebraization, natural proofs barriers suggest this is very hard)
3. Is accepted by the complexity theory community

No such proof has been found in Vega Delgado's work, or anywhere else.

---

## Formal Verification Results

Both the Lean and Rocq formalizations confirm:

1. **`owf_inversion_hard`** (hardness of inverting the candidate function): Cannot be proven without circularity or unsubstantiated claims. Marked as `sorry` (Lean) / `Admitted` (Rocq).

2. **`one_way_functions_exist`**: Depends on the above; also invalid.

3. The valid parts of the proof (the known theorem relating one-way functions to P vs NP) are correctly formalized and compile successfully.

---

## References

- **One-Way Functions**: Goldreich, O. (2001). "Foundations of Cryptography: Volume I, Basic Tools." Cambridge University Press.
- **P vs NP and OWF**: Impagliazzo, R. (1995). "A personal view of average-case complexity." 10th Annual Structure in Complexity Theory Conference.
- **Natural Proofs Barrier**: Razborov, A. & Rudich, S. (1994). "Natural proofs." STOC '94.
- **Woeginger's List**: Entry #68, https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
