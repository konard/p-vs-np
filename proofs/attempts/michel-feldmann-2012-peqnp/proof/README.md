# Forward Proof Formalization: Feldmann 2012

This directory contains the formal proof attempt following Feldmann's approach as faithfully as possible.

## Contents

- `lean/FeldmannProof.lean` - Lean 4 formalization
- `rocq/FeldmannProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Feldmann's claimed proof:

1. **Probabilistic Encoding**: Boolean variables encoded as conditional probabilities P(i) = P(X_i = 1 | Λ)
2. **Partial Requirements**: Conjunctions of literals with associated marginal probabilities
3. **LP Construction**: Specific equations from clauses + consistency equations from probability axioms
4. **Main Claim** (Proposition 7): LP feasibility ⟺ Boolean satisfiability
5. **Polynomial Size** (Proposition 2): O(N³·M) working unknowns for 3-SAT with N variables, M clauses
6. **Polynomial-Time Decision**: Using Khachiyan's ellipsoid method or Karmarkar's interior-point method

## The Attempted Proof Logic

Feldmann's argument proceeds:

1. **Encode** the SAT formula as a probability space over truth assignments
2. **Construct** the LP system from "specific equations" (one per clause) and "consistency equations"
3. **Claim** (Proposition 7): A satisfying assignment exists ⟺ the LP is feasible
4. **Invoke** polynomial-time LP solvers (Khachiyan 1979)
5. **Conclude** 3-SAT ∈ P, so P = NP

## Where the Formalizations Stop

The formalizations use `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Feldmann's argument fails. These mark locations where:

1. **Missing Construction Algorithm**: The step that builds the LP system from a SAT formula is claimed but has no polynomial-time algorithm.

2. **Uncomputed Working Unknowns**: Definition 3 specifies which partial requirements to track, but no procedure is given to enumerate them in polynomial time.

3. **Circular Verification**: Proposition 6 requires verifying the LP against all 2^N truth assignments — which is exponential.

4. **Computational Model Gap**: The real-arithmetic LP model differs from the discrete Turing machine model of complexity theory.

## See Also

- [`../README.md`](../README.md) — Overview of the attempt and error explanation
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) — Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) — Explanation of why the proof fails
