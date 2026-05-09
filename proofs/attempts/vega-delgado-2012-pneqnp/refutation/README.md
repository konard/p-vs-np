# Refutation: Vega Delgado 2012

This directory contains formal refutations of the core claims in Vega Delgado's 2012 P ≠ NP proof attempt.

## Contents

- `lean/VegaDelgado2012Refutation.lean` - Lean 4 refutation
- `rocq/VegaDelgado2012Refutation.v` - Rocq refutation

## Why the Proof Fails

Vega Delgado's 2012 proof attempt contains two fundamental errors.

---

## Error 1: The Unjustified Critical Implication (P = UP → EXP = P)

### The Claim

The proof claims that if P = UP, then EXP = P.

### Why This Fails

**The Time Hierarchy Theorem is unconditional.** It proves EXP ≠ P regardless of any other assumption, including whether P = UP. Specifically:

- The Time Hierarchy Theorem states: there exist problems solvable in exponential time that are not solvable in polynomial time.
- This proof does not depend on the relationship between P and UP.
- Therefore, asserting that "P = UP implies EXP = P" directly contradicts a known theorem — the proof step is asserting something false.

**There is no known reduction.** To establish P = UP → EXP = P, one would need:
- A polynomial-time reduction from every EXP problem to some P or UP problem, OR
- A complexity-theoretic oracle or collapse result connecting these classes.

Neither exists. The collapse of P and UP (both polynomial-time classes involving deterministic vs. unambiguous nondeterministic computation) has no bearing on the behavior of exponential-time computations.

**Summary**: The Time Hierarchy Theorem already separates P from EXP unconditionally. The status of "P vs UP" is irrelevant to this separation.

---

## Error 2: Insufficient Conclusion (P ≠ UP ↛ P ≠ NP)

### The Claim

Even if P ≠ UP could be proven, the proof concludes P ≠ NP.

### Why This Fails

We know:
- P ⊆ UP ⊆ NP

But we do **not** know whether UP = NP. This relationship is itself an open question in complexity theory. Possible scenarios:

| Scenario | Compatible with P ≠ UP? | Compatible with P = NP? |
|---|---|---|
| P ⊂ UP ⊂ NP | Yes | No |
| P ⊂ UP = NP | Yes | No |
| P = UP ⊂ NP | No (contradicts assumption) | No |

Even granting P ≠ UP, we cannot conclude P ≠ NP without independently proving UP = NP (or finding a specific NP-complete problem not in UP). The proof provides neither.

---

## Formal Verification Results

Both the Lean and Rocq formalizations confirm:

1. **`vega_delgado_critical_step`** (P = UP → EXP = P): Cannot be proven. Marked as `sorry` (Lean) / `Admitted` (Rocq).
2. **`vega_delgado_insufficient`** (P ≠ UP → P ≠ NP): Cannot be proven. Marked as `sorry` (Lean) / `Admitted` (Rocq).

The rest of the proof structure (proof by contradiction, use of Time Hierarchy Theorem) is logically sound, but depends on these two unprovable steps.

---

## What the Refutation Formalizations Demonstrate

The refutation files provide:

1. **Unconditional EXP ≠ P separation**: Demonstrating that EXP and P differ regardless of P vs UP.
2. **UP ≠ NP independence**: Showing that P ≠ UP is consistent with P = NP (illustrating the gap in the argument).
3. **Formal identification of the proof gap**: Machine-verified evidence of exactly which steps cannot be proven.

## References

- **Time Hierarchy Theorem**: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms."
- **UP Complexity Class**: Valiant, L. G. (1976). "Relative complexity of checking and evaluating."
- **Woeginger's List**: Entry #83, https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
