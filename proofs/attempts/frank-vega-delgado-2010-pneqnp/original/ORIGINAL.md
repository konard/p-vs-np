# Original Paper: A Solution to the P versus NP Problem (November 2010)

**Author:** Frank Vega Delgado
**Year:** 2010 (November)
**Title:** "A Solution to the P versus NP Problem"
**Claim:** P ≠ NP
**Woeginger's List:** Entry #68
**Source:** arXiv:1011.2730

---

## Reconstruction

The paper presents a search problem called `CERTIFYING`. Informally, the input is a deterministic Turing machine together with one of its outputs, and the task is to find an input that produces that output.

The abstract argument is:

1. `CERTIFYING` is in NP, because a candidate input can be checked by running the machine.
2. If `CERTIFYING` were in P, the paper claims that some undecidable language would be forced into NP.
3. Since NP languages are decidable, that would be impossible.
4. Therefore `CERTIFYING` is not in P.
5. Because `CERTIFYING` is in NP, the paper concludes that P ≠ NP.

---

## What the Paper Tries to Establish

The proof tries to move from a concrete search problem to a separation of complexity classes:

- It treats `CERTIFYING` as a problem whose positive instances have short certificates.
- It then tries to upgrade a polynomial-time algorithm for that problem into a statement about undecidable languages.
- The intended contradiction is that NP should not contain an undecidable language.

---

## Why This Reconstruction Is Incomplete

The key missing piece is the implication from `CERTIFYING ∈ P` to an undecidable language in NP.

The paper does not provide:

- a fully specified undecidable language,
- a valid reduction from `CERTIFYING`,
- or a proof that the reduction preserves the required computability properties.

So the reconstruction captures the paper's intended line of reasoning, but not a complete proof.

---

## Historical Note

Woeginger's entry #68 describes the paper in terms of the `CERTIFYING` problem and the claim that NP would otherwise contain an undecidable problem. The February 2012 attempt is different and is documented separately in [`../vega-delgado-2012-pneqnp/`](../vega-delgado-2012-pneqnp/).

---

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #68)
- arXiv:1011.2730, `A Solution to the P versus NP Problem`
- Related attempt: [`../vega-delgado-2012-pneqnp/`](../vega-delgado-2012-pneqnp/)
