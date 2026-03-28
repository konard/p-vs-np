# Salemi (2009) - Refutation

This directory contains formal refutations of the errors in Salemi's P=NP proof attempt.

## Critical Errors Identified

### Error 1: Saturation Complexity Not O(n^15)

**Claim**: The Saturation operation runs in O(n^15) time
**Error**: No proof that the number of iterations is polynomial

- Each iteration is O(n^9)
- Paper assumes O(n^3) iterations without justification
- Worst-case could require exponential iterations

### Error 2: Circular Reasoning in Theorem 11

**Claim**: Saturated non-empty CI3Sat has a constructible solution
**Error**: Proof assumes properties that Saturation must guarantee, but Saturation's correctness depends on Theorem 11

- Theorem 11 needs specific structural properties
- These properties are claimed to come from Saturation
- But Saturation's validity relies on Theorem 11
- Creates circular dependency

### Error 3: Construction Algorithm Not Proven Polynomial

**Claim**: The "Consistent Choice" algorithm builds solutions in polynomial time
**Error**: No proof of polynomial termination

- Each choice may require checking exponentially many rows
- Variable reordering complexity not analyzed
- Multiple valid choices may lead to exponential search

## Formalization Status

Currently, refutation axioms are included in the forward proof files:
- `error_1_saturation_not_polynomial`
- `error_2_circular_reasoning`
- `error_3_construction_not_polynomial`

Future work will separate these into dedicated refutation proofs showing:
- Counterexamples where Saturation requires exponential iterations
- Cases where circular reasoning fails
- Instances where construction requires exponential steps

## Educational Value

This refutation demonstrates:
- How subtle complexity analysis errors invalidate P=NP proofs
- The importance of proving iteration bounds, not just per-iteration complexity
- Why circular reasoning is fatal in constructive existence proofs
- How "intuitive polynomial behavior" differs from proven polynomial bounds
