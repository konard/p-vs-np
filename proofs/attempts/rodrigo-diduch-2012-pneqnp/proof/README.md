# Forward Proof Formalization: Rodrigo Diduch (2012)

This directory contains the formal proof attempt following Diduch's approach as faithfully as possible.

## Contents

- `lean/DiduchProof.lean` - Lean 4 formalization
- `rocq/DiduchProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Diduch's argument as stated in the paper:

1. **Definitions of P and NP**: Standard complexity-theoretic definitions
2. **The definitional argument**: P and NP have different definitions, so they should differ
3. **The intuitive hardness argument**: NP problems appear hard, so P ≠ NP
4. **What a lower bound would require**: Formal structure of a valid P ≠ NP proof

## The Attempted Proof Logic

Diduch's argument proceeds:

1. **Define P**: Problems solvable by a deterministic TM in polynomial time
2. **Define NP**: Problems verifiable by a deterministic TM in polynomial time given a certificate
3. **Observe the definitional gap**: P solves, NP verifies — these sound different
4. **Conclude**: Therefore P ≠ NP (a "categorical NO")

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the
critical gaps where Diduch's argument fails. These mark locations where:

1. **Definitions ≠ Extensions**: Having different definitions does not prove the classes
   have different members — this leap cannot be formalized without additional proof
2. **Observation ≠ Lower Bound**: Observing that no polynomial algorithm is known does not
   prove that none exists — this gap cannot be closed by informal argument
3. **Missing Lower Bound**: The core requirement — showing ∀ TM deciding SAT, time(TM)
   is super-polynomial — is simply not present in the paper

## The Core Error

Diduch's argument confuses:

- **Epistemological gap**: "We don't know a polynomial algorithm for SAT"
- **Ontological gap**: "No polynomial algorithm for SAT can exist"

The former is an observation about current knowledge; the latter is what P ≠ NP means
and what must be proven. The formalization makes this gap explicit and precise.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
