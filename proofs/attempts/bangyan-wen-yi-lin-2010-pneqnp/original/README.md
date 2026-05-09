# Bangyan Wen & Yi Lin (2010) - Original Source Reconstruction

**Attempt ID**: 70 (from Woeginger's list)
**Authors**: Bangyan Wen & Yi Lin
**Year**: 2010
**Claim**: P ≠ NP
**Source**: *Scientific Inquiry - A Journal of the IIGSS*, Vol. 11, No. 2, December 2010

## Source Status

The paper "THE ANSWER TO THE P/NP PROBLEM IS P≠NP!" is referenced by Woeginger's
P versus NP list, but the live journal page does not provide a stable freely
accessible copy of the full article. This directory therefore keeps the best
English reconstruction we can recover from the available references.

If a stable PDF or HTML copy of the original article becomes available later, it
should be archived here alongside `ORIGINAL.md`.

## Reconstructed Core Idea

The attempt argues that P and NP differ because they are described by different
logical forms:

1. P is associated with deterministic polynomial-time computation.
2. NP is associated with polynomial-size certificates and verification.
3. The certificate space is exponential in the certificate length.
4. Naive enumeration over that space is therefore exponential.
5. Therefore no deterministic polynomial-time algorithm can decide NP.
6. Conclusion: P ≠ NP.

The paper presents this as "formal logic reasoning and analysis" rather than as
a lower-bound proof on a specific NP-complete problem.

## Why The Reconstruction Fails

The missing step is the inference from exponential search space to a lower bound
for all deterministic algorithms. That inference is not valid:

- Many problems have exponentially many candidate witnesses but are still in P.
- The paper does not produce a specific hard language in NP and prove a lower bound.
- The argument does not address known barriers such as relativization.
- The quantifier asymmetry between P and NP is the statement of the problem, not a proof.

## Files

- [`ORIGINAL.md`](ORIGINAL.md) - English reconstruction of the paper's content
- [`../README.md`](../README.md) - Full attempt overview and refutation
- [`../proof/README.md`](../proof/README.md) - Forward formalization of the claimed argument
- [`../refutation/README.md`](../refutation/README.md) - Formal refutation of the argument
