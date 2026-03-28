# Forward Proof Formalization: Hofman 2006

This directory contains the formal proof attempt following Hofman's approach as faithfully as possible.

## Contents

- `lean/HofmanProofAttempt.lean` - Lean 4 formalization
- `rocq/HofmanProofAttempt.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **The cSAT Problem Definition**: The counted Boolean satisfiability problem as defined by Hofman
2. **The Measure Predicate mu**: Counting satisfying assignments via inclusion-exclusion
3. **Boolean Algebra Axioms (Ax1-Ax23)**: The axiom system Hofman uses
4. **FOPC Transformation Model**: The claim that algorithms must follow FOPC axiom sequences
5. **The Lower Bound Argument**: Theorem 5 stating lower bound equals minimal transformation cost

## The Attempted Proof Logic

Hofman's argument proceeds:

1. **Define cSAT**: Given Boolean formula phi and threshold L (in unary), does phi have >= L satisfying assignments?
2. **Measure predicate mu**: Use inclusion-exclusion to count satisfying assignments
3. **FOPC analysis**: Claim any deterministic algorithm must correspond to FOPC transformations
4. **Lower bound**: Show all FOPC transformations require exponential time (Table 3 analysis)
5. **Conclusion**: Therefore P != NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Hofman's argument fails. These mark locations where:

1. The leap from proof complexity to computational complexity is made without justification
2. The restriction to FOPC transformations is assumed without proof
3. The circular reasoning in Theorem 5 becomes explicit

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
