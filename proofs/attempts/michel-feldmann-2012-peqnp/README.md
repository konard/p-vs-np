# Michel Feldmann (2012) - P=NP via Bayesian Inference

**Attempt ID**: 90 (from Woeginger's list)
**Author**: Michel Feldmann
**Year**: 2012 (revised 2020)
**Claim**: P = NP
**Paper**: "Solving satisfiability by Bayesian inference"
**arXiv**: [1205.6658v5](https://arxiv.org/abs/1205.6658)
**Status**: Refuted

## Summary

Michel Feldmann claims to prove P=NP by using Bayesian inference to solve 3-SAT in polynomial time. The approach converts Boolean satisfiability problems into linear programming (LP) problems through a probabilistic encoding, arguing that LP feasibility decides satisfiability and can be checked in polynomial time.

## Main Argument

### The Approach

1. **Probabilistic Encoding**: Convert Boolean variables into probabilities in a Kolmogorov probability space. Each variable X_i gets probability P(i) = P(X_i = 1 | Λ).

2. **LP Construction**: Translate each SAT clause into "specific equations" relating the probabilities. Add "consistency equations" to enforce valid probability distributions. Together, these form a linear programming system.

3. **Equivalence Claim** (Proposition 7): For "strict satisfiability" problems, LP feasibility is equivalent to Boolean satisfiability.

4. **Polynomial-Time Conclusion**: Since LP feasibility is decidable in polynomial time (Khachiyan 1979, Karmarkar 1984), and the LP has polynomial size (Proposition 2), 3-SAT ∈ P, so P = NP.

## The Error

### Fundamental Flaw: Missing Construction Algorithm

The proof contains a **fundamental gap**: it never provides a polynomial-time algorithm to construct the LP system from a SAT formula.

Feldmann's argument structure:

```
Input: SAT formula f
Step 1: Construct LP system C(f)     ← ALGORITHM MISSING
Step 2: Check LP feasibility          ← Proven polynomial (Khachiyan 1979)
Output: Satisfiability of f
```

**Step 2** is correct and well-known. **Step 1** is never proven to be polynomial-time computable.

### The Three Unproven Requirements

To construct the LP system C(f) correctly, one must:

1. **Determine "working unknowns"** — which partial probability requirements to track. The paper claims this set has polynomial size (Proposition 2) but provides **no algorithm** to compute this set.

2. **Build "consistency equations"** — ensuring all probability constraints are captured. Depends on step 1, which is uncomputed.

3. **Verify correctness** — Proposition 6 requires checking all 2^N truth assignments to confirm the LP correctly encodes the formula. This is explicitly exponential.

### The Circular Reasoning

To construct C(f) correctly, we must understand which partial requirements appear in satisfying assignments — but determining this structure is equivalent to solving SAT itself. The proof is circular:

- To construct the LP, we need to know the satisfiability structure of f
- To know the satisfiability structure, we need to solve SAT
- But solving SAT is what the LP construction is supposed to enable

### Computational Model Mismatch

Feldmann's framework uses **exact real arithmetic** (continuous probability distributions, convex optimization). Standard complexity theory measures computation on Turing machines with **discrete symbols**. These are different computational models, and polynomial time in real arithmetic does not imply polynomial time on a Turing machine.

### What Feldmann Actually Proved

- ✓ **Proved**: There exists a correspondence between SAT formulas and LP systems such that feasibility ↔ satisfiability (interesting but not sufficient)
- ✓ **Proved**: If the LP system is given, checking feasibility is polynomial-time (already known since 1979)
- ✗ **Not Proved**: The LP system can be constructed from a SAT formula in polynomial time
- ✗ **Not Proved**: P = NP

## Files

```
michel-feldmann-2012-peqnp/
├── README.md              ← This file (overview and error explanation)
├── ORIGINAL.md            ← Markdown conversion of the paper
├── ORIGINAL.pdf           ← Original paper PDF (arXiv:1205.6658)
├── proof/
│   ├── README.md          ← Explanation of the forward formalization
│   ├── lean/
│   │   └── FeldmannProof.lean  ← Lean 4 forward proof attempt
│   └── rocq/
│       └── FeldmannProof.v     ← Rocq forward proof attempt
└── refutation/
    ├── README.md          ← Explanation of the refutation
    ├── lean/
    │   └── FeldmannRefutation.lean  ← Lean 4 refutation
    └── rocq/
        └── FeldmannRefutation.v     ← Rocq refutation
```

- [`ORIGINAL.pdf`](ORIGINAL.pdf) — Original paper from arXiv
- [`ORIGINAL.md`](ORIGINAL.md) — Markdown conversion of the paper
- [`proof/`](proof/) — Forward formalization of Feldmann's argument
- [`refutation/`](refutation/) — Formalization of the proof gaps

## References

1. Feldmann, M. (2020). "Solving satisfiability by Bayesian inference." arXiv:1205.6658v5
2. Cook, S. (1971). "The complexity of theorem proving procedures." STOC 1971.
3. Karp, R. (1972). "Reducibility among combinatorial problems."
4. Khachiyan, L. (1979). "A polynomial algorithm in linear programming."
5. Woeginger, G. "The P-versus-NP page" — Entry #90: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
