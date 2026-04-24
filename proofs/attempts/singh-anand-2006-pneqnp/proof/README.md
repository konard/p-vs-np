# Forward Proof Formalization: Singh Anand (2006)

This directory contains the formal proof attempt following Anand's argument as faithfully as possible.

## Contents

- `lean/SinghAnandProof.lean` - Lean 4 formalization
- `rocq/SinghAnandProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations follow Anand's argument step by step:

1. **Formula G(x)**: Formalizing `G(x) := x = 0 ∨ ∃y, x = S(y)` — every element is 0 or a successor.
2. **Base case**: G(0) is trivially provable (x = 0 is satisfied).
3. **Inductive step**: G(x) → G(S(x)) is provable (S(x) is a successor by definition).
4. **Induction conclusion**: (∀x)G(x) is provable in PA.
5. **Anand's inference**: (∀x)G(x) is provable → PA has no non-standard models.
6. **Complexity connection**: No non-standard models → P ≠ NP.

## Where the Formalizations Stop

Step 5 is where the argument breaks down. The formalizations mark the invalid inference with `sorry` (Lean) and `Admitted` (Rocq):

- **The flaw**: Proving (∀x)G(x) does not show PA has no non-standard models. By Gödel's Completeness Theorem, this formula holds in ALL models—including non-standard ones.
- **What G(x) actually shows**: Every element is either 0 or a successor of something. In non-standard models, non-standard elements are successors of other non-standard elements, so they satisfy G(x) too.

## The Argument Structure (Following the Original Paper)

```
From the paper (paraphrased):

1. Define G(x) := x = 0 ∨ ∃y, x = S(y)
2. G(0) is PA-provable [base case]
3. G(x) → G(S(x)) is PA-provable [inductive step]
4. By PA induction axiom: (∀x)G(x) is PA-provable
5. ❌ INVALID: (∀x)G(x) provable → no non-standard elements exist
6. ❌ INVALID: No non-standard models → P ≠ NP
```

Step 5 cannot be formalized without `sorry`/`Admitted` because it is logically incorrect.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Markdown reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Detailed explanation of why the proof fails
