# Forward Proof Formalization: Frank Vega (2015)

This directory contains formal proof attempts following Vega's argument as faithfully as possible.

## Contents

- `lean/VegaProof.lean` — Lean 4 formalization
- `rocq/VegaProof.v` — Rocq formalization

## What These Formalizations Capture

The formalizations attempt to encode each step of Vega's argument:

### Definition 3.1: The ∼P Class

A language L belongs to ∼P if:
```
L = {(x, y) : ∃z such that M₁(x,z) = "yes" and M₂(y,z) = "yes" where x ∈ L₁ and y ∈ L₂}
```
where L₁, L₂ ∈ P and M₁, M₂ are their respective verifiers.

### Definition 4.1: E-Reduction

L₁ ≤∼ L₂ if there exist two log-space computable functions f and g such that:
```
(x, y) ∈ L₁ ⟺ (f(x), g(y)) ∈ L₂
```

### Theorem 4.2: ∼P is Closed Under E-Reductions

If L ≤∼ L' and L' ∈ ∼P, then L ∈ ∼P.

### Definition 5.1 and Theorem 5.2: ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT

The reduction maps each clause (x ∨ y ∨ z) to:
- Qᵢ = (x ⊕ y ⊕ z) for XOR 3SAT
- Pᵢ = (¬x ∨ ¬y) ∧ (¬y ∨ ¬z) ∧ (¬x ∨ ¬z) for 2SAT

### Theorem 5.3: ∼P = NP

Claimed to follow from Theorem 5.2 and closure under reductions.

### Theorem 6.1: ∼HORNSAT ∈ ∼P

∼HORNSAT = {(φ, φ) : φ ∈ HORNSAT} is claimed to be in ∼P.

### Theorem 6.2: ∼P = P

Claimed to follow from Theorem 6.1 and closure under reductions.

### Theorem 6.3: P = NP

Claimed to follow from Theorems 5.3 and 6.2.

## Where the Formalizations Stop

The key theorems are marked with `sorry` (Lean) and `Admitted` (Rocq) at the points where Vega's argument fails:

1. **Theorem 5.3**: The step from "∼ONE-IN-THREE 3SAT reduces to something in ∼P" to "∼P = NP" is unjustified. The formalizations cannot prove this without additional assumptions.

2. **Theorem 6.1 backward direction**: When trying to verify that the definition of ∼P captures exactly ∼HORNSAT = {(φ,φ) : φ ∈ HORNSAT}, the backward direction requires showing x = y from the ∼P conditions, which cannot be derived since shared certificates are vacuous for P problems.

3. **Theorem 6.2**: Same issue as 5.3 — showing one P-complete problem is in ∼P does not imply ∼P = P.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) — Full text of the original paper
- [`../refutation/README.md`](../refutation/README.md) — Explanation of why the proof fails
