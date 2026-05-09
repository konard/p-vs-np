# Forward Proof Formalization: Vega Delgado 2012

This directory contains the formal proof attempt following Vega Delgado's approach as faithfully as possible.

## Contents

- `lean/VegaDelgado2012Proof.lean` - Lean 4 formalization
- `rocq/VegaDelgado2012Proof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **Complexity Class Definitions**: Formal definitions of P, UP, NP, and EXP
2. **Time Hierarchy Theorem**: Stated as an axiom (well-known result: EXP ≠ P)
3. **Proof by Contradiction Structure**: The claimed argument from P = UP to EXP = P to contradiction
4. **Critical Gap Identification**: The step "P = UP → EXP = P" is marked as unprovable

## The Attempted Proof Logic

Vega Delgado's argument proceeds:

1. **Assume** P = UP (unambiguous nondeterminism equals determinism at polynomial level)
2. **Derive** EXP = P (claimed consequence — the CRITICAL FAILING STEP)
3. **Contradict** Time Hierarchy Theorem (which proves EXP ≠ P)
4. **Conclude** P ≠ UP by reductio ad absurdum
5. **Final Claim**: Since UP ⊆ NP and P ≠ UP, therefore P ≠ NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) / `Admitted` (Rocq) placeholders at the critical gaps where the argument fails:

1. **Step 2 fails** (`vega_delgado_critical_step`): The claim that P = UP → EXP = P has no known complexity-theoretic justification.
   - P and UP are both polynomial-time classes; their equality tells us nothing about exponential-time computation.
   - There is no known reduction from EXP problems to UP problems.
   - This cannot be proven without violating the Time Hierarchy Theorem (which is what the proof tries to use as a contradiction tool).

2. **Step 5 fails** (`vega_delgado_insufficient`): Even if P ≠ UP were established, this does not imply P ≠ NP.
   - We only know UP ⊆ NP, but whether UP = NP is itself an open problem.
   - P ≠ UP does not rule out the possibility that P = NP (if, for instance, NP collapses to P).

## The Core Error

The core error is the unjustified leap from "P = UP" to "EXP = P":

| What We Know | What Is Needed |
|---|---|
| P ⊆ UP ⊆ NP ⊆ EXP | A mechanism connecting UP to EXP |
| EXP ≠ P (Time Hierarchy) | Reduction from EXP to P or UP |
| Collapse of P and UP | Same — there is no such reduction |

The relationship between P and UP involves only polynomial-time computation. No known result connects the P = UP question to the EXP vs P question. In fact, the Time Hierarchy Theorem already guarantees EXP ≠ P independently of any relationship between P and UP.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Description of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
- [`../README.md`](../README.md) - Overview of the attempt
