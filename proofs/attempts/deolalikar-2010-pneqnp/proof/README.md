# Proof Formalization: Deolalikar's P≠NP Attempt (2010)

This directory contains a forward formalization of Deolalikar's claimed proof that P ≠ NP.

## What Is Being Formalized

We formalize Deolalikar's *claimed* argument as faithfully as possible, using axioms for the steps that cannot be directly proved (because the proof is ultimately flawed). The goal is to make explicit exactly which steps require axioms, so that the gaps become visible in the formal system.

## Deolalikar's Claimed Proof Strategy

1. **FO+LFP characterizes P** (Immerman-Vardi theorem — sound)
2. **Gaifman locality of FO** (Gaifman's theorem — sound)
3. **Claimed extension**: FO+LFP formulas can only define "polylog-parameterizable" solution spaces (UNPROVEN — this is the critical gap)
4. **Statistical physics**: Random k-SAT in the hard phase has non-polylog-parameterizable solution spaces (CLAIMED but not rigorously proved)
5. **Conclusion**: k-SAT ∉ P, hence P ≠ NP

## Files

- `lean/DeolalikarProof.lean` — Lean 4 formalization
- `rocq/DeolalikarProof.v` — Rocq/Coq formalization

## Status

The formalization captures the *structure* of Deolalikar's argument. The steps that Deolalikar could not prove are marked as `axiom` (Lean) or `Axiom` (Rocq). The key unproved steps are:

- `deolalikar_fo_lfp_polylog_parameterizable`: That FO+LFP formulas produce polylog-parameterizable solution spaces
- `deolalikar_hard_ksat_not_parameterizable`: That hard k-SAT solution spaces are not polylog-parameterizable
- `deolalikar_transfer`: That the statistical property of random k-SAT transfers to a complexity lower bound

These axioms represent the gaps in Deolalikar's proof. See the `refutation/` directory for why these claims are problematic.
