# Refutation Formalization

This directory contains formalization of the refutation of Aslam's proof attempt.

## Files

- **lean/AslamRefutation.lean**: Lean 4 formalization of the refutation (to be added)
- **rocq/AslamRefutation.v**: Rocq (Coq) formalization of the refutation (to be added)

## The Refutation

The refutation (arXiv:0904.3912) demonstrates that Aslam's algorithm does not correctly count perfect matchings.

### Key Points

1. **Counter-Example Exists**: There exists a specific graph G for which Aslam's algorithm produces an incorrect count
2. **Not Universal**: The algorithm may work on some graphs but fails on others
3. **Fundamental Flaw**: The MinSet Sequence structure does not correctly represent all perfect matchings

### What Would Be Formalized

A complete refutation formalization would include:

1. **Counter-Example Graph**: A specific bipartite graph G
2. **Expected Count**: The correct number of perfect matchings in G
3. **Aslam's Algorithm Output**: What Aslam's algorithm claims for G
4. **Proof of Mismatch**: Formal verification that these differ

### Current Status

The refutation is currently represented axiomatically in the proof formalization:
```lean
axiom refutation_counter_example :
  ∃ ce : CounterExample, ce.aslamCount ≠ ce.expectedCount
```

This axiom captures the existence of the counter-example from the refutation paper without fully constructing it.

## Why Counter-Examples Matter

In complexity theory:
- A claim of "for all graphs G, algorithm A correctly counts matchings" is a universal statement
- A single counter-example is sufficient to refute such a claim
- The existence of the counter-example proves the algorithm is incorrect

## References

- **Refutation Paper**: "Refutation of Aslam's Proof that NP = P" (2009)
  - arXiv:0904.3912
  - Available at: https://arxiv.org/abs/0904.3912

- **Aslam's Response**: "Further Refinements..." (2009)
  - arXiv:0906.5112
  - Available at: https://arxiv.org/abs/0906.5112
