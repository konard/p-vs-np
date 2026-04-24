# Frank Vega Delgado (2010) - Original Paper

**Navigation:** [↑ Back to Attempt Overview](../README.md) | [Woeginger Entry #68](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Overview

This folder reconstructs the November 2010 paper `A Solution to the P versus NP Problem` (arXiv:1011.2730). The paper claims to solve P vs NP by studying a problem called `CERTIFYING`.

The core claim is:

1. `CERTIFYING` is in NP because a proposed preimage can be checked efficiently.
2. If `CERTIFYING` were in P, then NP would contain an undecidable language.
3. Since NP languages are decidable, this is claimed to be impossible.
4. Therefore `CERTIFYING ∉ P`, and P ≠ NP.

The formal refutation in [`../refutation/README.md`](../refutation/README.md) explains why the decisive implication is not established.

---

## Source Material

- `ORIGINAL.pdf` - the source arXiv paper
- `ORIGINAL.md` - Markdown reconstruction of the argument

---

## Notes

The paper does not provide a fully rigorous reduction from `CERTIFYING ∈ P` to an undecidable language in NP. That missing step is the point where the formalization stops and the refutation begins.
