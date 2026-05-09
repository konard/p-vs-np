# Forward Proof Formalization: Stefan Jaeger (2011)

This directory contains the formalization of Stefan Jaeger's claimed proof from "Computational Complexity on Signed Numbers" (arXiv:1104.2538).

## Overview

Jaeger's paper makes two complexity claims using "b-numbers" (binary numbers with a sign bit encoding uncertainty about the existence of zero):

1. **Theorem 3 (P theorem)**: With the first Peano axiom, P = NP
2. **Theorem 4 (PNP theorem)**: Without the first Peano axiom, P ⊊ NP

## What We Formalize

The Lean and Rocq files formalize:

- The definition of b-numbers and the sign bit (`b_0`)
- The Shannon entropy function `I(p)`
- **Theorem 1 (Entropy theorem)**: Bounds on `E(b)`
- **Corollary 1**: All b-number computations are uncertain
- **Theorem 2 (Entropy reduction)**: Uncertainty can be reduced by adding bits
- **Theorem 3**: Jaeger's claimed P=NP result (formalized as stated; the flaw is documented)
- **Theorem 4**: Jaeger's claimed P≠NP result (formalized as stated; the flaw is documented)

## Status

Most theorems can be stated formally, but:
- **Theorem 3** as stated does not actually prove P=NP in the standard sense — it proves that a machine can terminate after padding the input, which is not the same as correctly deciding an NP-complete language. This is documented in comments.
- **Theorem 4** relies on an informal diagonal argument that does not hold up to formal scrutiny. The machine T is claimed to be in NP (by spending O(2^n) steps), but the claim that it is not in P rests on an unclear self-referential argument. This is documented in comments.

## Files

- `lean/JaegerProof.lean` — Lean 4 formalization
- `rocq/JaegerProof.v` — Rocq (Coq) formalization
