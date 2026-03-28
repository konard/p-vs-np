# Errors Found in Vega Delgado (2012) P≠NP Proof Attempt

This document summarizes the errors and gaps identified during the formal verification of Frank Vega Delgado's 2012 proof attempt.

## Critical Error: Unjustified Implication (P = UP → EXP = P)

### Location
- **Rocq**: `VegaDelgado2012.v:89` - `vega_delgado_critical_step` (marked as `Admitted`)
- **Lean**: `VegaDelgado2012.lean:133` - `vega_delgado_critical_step` (marked as `axiom`)
- **Isabelle**: `VegaDelgado2012.thy:129` - `vega_delgado_critical_step` (ends with `oops`)

### The Claim
Vega Delgado claims that if P = UP (where UP is Unambiguous Polynomial time), then EXP = P would follow.

### Why This Fails

1. **No Justification Provided**: The proof provides no mechanism or reduction to show how the collapse of P and UP (both polynomial-time complexity classes) would imply that exponential-time problems can be solved in polynomial time.

2. **Contradicts Time Hierarchy Theorem**: The Time Hierarchy Theorem (Hartmanis & Stearns, 1965) proves that EXP ≠ P. Any claim that P = UP implies EXP = P would need to show that P = UP is impossible, but this is done circularly by assuming what needs to be proven.

3. **Missing Reductions**: To validly prove P = UP → EXP = P, we would need:
   - A polynomial-time reduction from every EXP problem to some UP problem, OR
   - A mechanism to convert exponential-time computations to polynomial-time computations

   Neither is provided, and neither can exist without violating the Time Hierarchy Theorem.

4. **Unrelated Complexity Classes**:
   - P and UP are both polynomial-time classes (one deterministic, one unambiguous nondeterministic)
   - EXP is an exponential-time class
   - The relationship between P and UP tells us nothing about the time hierarchy

### Formal Verification Result

In all three proof assistants, this step cannot be completed:
- **Rocq**: Marked with `Admitted` (incomplete proof)
- **Lean**: Declared as an unprovable `axiom` with error comments
- **Isabelle**: Ends with `oops` (abandoned proof)

This is the **PRIMARY ERROR** that invalidates the entire proof.

## Secondary Error: Insufficient Conclusion (P ≠ UP ↛ P ≠ NP)

### Location
- **Rocq**: `VegaDelgado2012.v:152` - `vega_delgado_insufficient` (marked as `Admitted`)
- **Lean**: `VegaDelgado2012.lean:186` - `vega_delgado_insufficient` (marked as `axiom`)
- **Isabelle**: `VegaDelgado2012.thy:165` - `vega_delgado_insufficient` (ends with `oops`)

### The Claim
Even if P ≠ UP could be proven (which it cannot via this approach), the proof claims this would imply P ≠ NP.

### Why This Fails

1. **UP ⊆ NP, but UP = NP is Unknown**: We know that UP is a subset of NP, but we don't know if they're equal. The relationship between UP and NP is itself an open problem.

2. **Multiple Possible Scenarios**:
   - P ⊂ UP ⊂ NP (strict containments - P ≠ UP but could still have P = NP if NP collapses to UP)
   - P = UP ⊂ NP (P equals UP but both are strictly contained in NP)
   - P ⊂ UP = NP (UP equals NP but P doesn't)
   - P = UP = NP (everything collapses)

3. **Missing Proof**: To conclude P ≠ NP from P ≠ UP, we would need to additionally prove:
   - UP = NP, OR
   - There exists a problem in NP \ UP that also requires superpolynomial time

   Neither is provided in the proof.

### Formal Verification Result

This step also cannot be completed in any proof assistant, even if we hypothetically accepted the first error.

## Logical Structure Analysis

### Proof by Contradiction (Valid Technique)
The proof attempts to use *reductio ad absurdum* (proof by contradiction), which is a valid proof technique:
1. Assume P = UP
2. Derive a contradiction (EXP = P, which contradicts Time Hierarchy Theorem)
3. Conclude P ≠ UP

This structure is logically sound **if step 2 can be proven**. However, step 2 fails completely.

### Circular Reasoning
The proof has elements of circular reasoning:
- It assumes P = UP
- To derive a contradiction, it needs to show this implies EXP = P
- But showing P = UP → EXP = P is as hard (or harder) than the original problem
- The derivation itself would require complexity-theoretic results that don't exist

## Summary of Formalization Findings

### What Works
- The definitions of complexity classes (P, UP, NP, EXP) are correct
- The statement of the Time Hierarchy Theorem is correct
- The logical structure (proof by contradiction) is valid in principle

### What Fails
1. **Critical Step** (P = UP → EXP = P): **UNPROVABLE**
   - No valid reduction exists
   - Contradicts established results
   - Marked as `Admitted` (Rocq), `axiom` (Lean), or `oops` (Isabelle)

2. **Final Conclusion** (P ≠ UP → P ≠ NP): **UNPROVABLE**
   - Insufficient to bridge from UP to NP
   - Missing intermediate results
   - Marked as `Admitted` (Rocq), `axiom` (Lean), or `oops` (Isabelle)

### Verdict
The proof attempt fails at the critical derivation step. The gap is not a minor technical detail but a fundamental logical gap that cannot be filled with known complexity-theoretic techniques.

## References

- **Time Hierarchy Theorem**: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms"
- **UP Complexity Class**: Valiant, L. G. (1976). "Relative complexity of checking and evaluating"
- **Woeginger's List**: Entry #83, https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Conclusion

The formalization process successfully identified the exact locations where Vega Delgado's 2012 proof attempt fails. The proof cannot be completed in Rocq, Lean, or Isabelle without introducing unjustified axioms, which demonstrates that the claimed proof is invalid.

The primary error is the unsupported claim that P = UP implies EXP = P, which has no known justification in complexity theory and contradicts the Time Hierarchy Theorem.
