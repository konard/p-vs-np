# Refutation: Vega Delgado 2010

This directory contains formal refutations of the core claims in Vega Delgado's November 2010 `CERTIFYING`-based proof attempt.

## Contents

- `lean/VegaDelgado2010Refutation.lean` - Lean 4 refutation
- `rocq/VegaDelgado2010Refutation.v` - Rocq refutation

## Why the Proof Fails

Vega Delgado's 2010 proof attempt hinges on a single unsupported implication:

1. `CERTIFYING` is in NP.
2. If `CERTIFYING` were in P, then some undecidable language would be in NP.
3. That would contradict the fact that NP languages are decidable.

The problem is step 2. The paper does not supply a valid reduction or a formal machine argument that turns `CERTIFYING ∈ P` into an undecidable NP language.

---

## The Central Error: Missing Reduction

The decisive step would need to show:

```text
CERTIFYING ∈ P  ⇒  ∃ U, Undecidable(U) ∧ U ∈ NP
```

But the paper does not establish this implication.

What the paper actually shows is much weaker:

- A candidate input can be checked efficiently, so `CERTIFYING` looks like an NP-style relation.
- That fact alone does not manufacture an undecidable language.
- Without the missing reduction, there is no contradiction.

---

## Why This Matters

NP contains only decidable languages. So, if the paper had genuinely proved that an undecidable language belonged to NP, that would indeed be a contradiction.

However, the paper never bridges the gap from a search problem to undecidability:

- It does not specify the undecidable language precisely enough.
- It does not prove a reduction from `CERTIFYING`.
- It does not justify why a polynomial-time solver for `CERTIFYING` would change decidability.

---

## Formal Verification Results

Both the Lean and Rocq formalizations confirm:

1. `CERTIFYING` can be treated as an NP-style problem.
2. The step from `CERTIFYING ∈ P` to an undecidable language in NP is the missing piece.
3. The rest of the contradiction depends entirely on that missing piece.

The refutation files therefore stop exactly where the original proof stops being rigorous.

---

## References

- **Woeginger's List**: Entry #68, https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Original paper**: arXiv:1011.2730, `A Solution to the P versus NP Problem`
- **Computability background**: decidable vs. undecidable languages
