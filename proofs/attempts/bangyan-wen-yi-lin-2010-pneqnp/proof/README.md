# Forward Proof Formalization: Wen & Lin 2010

This directory contains the formal proof attempt following Wen & Lin's approach as faithfully as possible.

## Contents

- `lean/WenLinProof.lean` - Lean 4 formalization
- `rocq/WenLinProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture the paper's formal logic argument:

1. **Logical Characterization of P**: P problems have a deterministic poly-time algorithm, with a unique computation path.
2. **Logical Characterization of NP**: NP problems have poly-time verifiable certificates, with the certificate ranging over an exponential-size domain.
3. **Asymmetry Claim**: The existential quantifier in NP ranges over 2^p(n) possible certificates, while P has a unique deterministic computation.
4. **Naive Enumeration**: Searching all certificates takes 2^p(n) * p(n) time — exponential.
5. **The Claimed Conclusion**: Therefore no polynomial-time algorithm can decide NP problems.

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gap where the paper's argument fails:

- **The Invalid Inference**: The step from "naive search is exponential" to "no poly-time algorithm exists" is marked as unprovable from the given premises (it requires P ≠ NP itself).
- **The Central Theorem**: `wen_lin_main_claim` is marked `sorry`/`Admitted` because it IS the P ≠ NP conjecture, not a consequence of the stated premises.

## The Core Error

The paper treats the following as a valid logical deduction:
```
(1) Certificate search space is exponential      [TRUE]
(2) Naive enumeration over it is exponential     [TRUE]
(3) Therefore no poly-time algorithm exists      [NOT PROVED — requires P ≠ NP]
```

Step (3) does not follow from (1)-(2). Many problems with exponential candidate spaces
are still solvable in polynomial time (graph reachability, linear programming, max matching).
The paper provides no argument ruling out such structural polynomial-time algorithms for NP problems.
