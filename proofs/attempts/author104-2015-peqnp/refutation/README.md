# Refutation: Frank Vega (2015)

This directory contains formal demonstrations of why Vega's proof fails.

## Contents

- `lean/VegaRefutation.lean` — Lean 4 refutation
- `rocq/VegaRefutation.v` — Rocq refutation

## The Core Errors

### Error 1: Type Mismatch (Primary Error)

Vega's central claim is that ∼P = NP and ∼P = P. However:
- **∼P** is a class of languages over **ordered pairs** (x, y)
- **P** and **NP** are classes of languages over **single strings** x

These are fundamentally different types. The claim "∼P = NP" is a type error — it is
like saying "the set of pairs of integers equals the set of integers."

**Formal consequence:** The theorems "∼P = P" and "∼P = NP" cannot even be stated
in a formally correct way without additional bridging definitions. Vega does not provide
such definitions.

### Error 2: Subset vs. Equality

Even if we interpret Vega's claim as:
> For every L ∈ NP, the diagonal embedding {(x,x) : x ∈ L} is in ∼P

This only shows:
- NP ⊆ {L : DiagonalEmbedding(L) ∈ ∼P}
- P ⊆ {L : DiagonalEmbedding(L) ∈ ∼P}

Showing two sets both have subsets in a third set does NOT prove the two sets are equal.

**Formal consequence:** The following counterexample structure shows the error:
```
Let A = {apple}, B = {orange}, C = {apple, orange}
Then A ⊆ C and B ⊆ C, but A ≠ B
```

### Error 3: Vacuous Certificates for P Problems

Vega's Definition 3.1 requires verifiers M₁, M₂ for L₁, L₂ ∈ P with a "shared certificate z."
However, for problems in P:
- Membership can be decided without any certificate
- Any certificate can be trivially accepted (just ignore it and run the decider)
- The "shared certificate" condition provides zero information

**Formal consequence:** The definition of ∼P, when applied to problems in P, admits
ALL pairs (x, y) where x ∈ L₁ and y ∈ L₂ (the shared certificate is always trivially
satisfiable). This makes the definition degenerate.

### Error 4: Diagonal Constructions Don't Preserve Reduction Structure

Vega claims that because ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT and 3XOR-2SAT ∈ ∼P,
we can apply closure under reductions to show ∼P = NP.

However:
- The diagonal embedding DiagonalEmbedding(L) = {(x,x) : x ∈ L} does not preserve polynomial-time reductions
- If L₁ ≤ᵖ L₂ via function f, then DiagonalEmbedding(L₁) does NOT e-reduce to DiagonalEmbedding(L₂)
  via the same function (one would need to apply f to BOTH components)
- Therefore, closure under e-reductions cannot be used to show that all NP problems can
  be diagonally embedded in ∼P

**Formal consequence:** The reduction structure argument breaks down when passing
from the pair-language domain to the single-string domain.

### Error 5: Incorrect Completeness Argument

Vega argues:
1. ∼ONE-IN-THREE 3SAT is NP-complete → ∼P contains an NP-complete problem → ∼P = NP
2. ∼HORNSAT is P-complete → ∼P contains a P-complete problem → ∼P = P

This misapplies the standard argument. The standard argument says:
> If C is closed under reductions and L_C ∈ C is complete for class D,
> then C = D (assuming D ⊆ C or C ⊆ D is shown both ways).

Vega shows only one direction (embedding), not the reverse, and the closure argument
requires the types to match (e-reductions for ∼P ≠ polynomial-time reductions for NP).

## Why This Error Is Typical

This attempt exhibits a common pattern in P vs NP attempts:
1. Define a new complexity class C
2. Show P ⊆ C and NP ⊆ C via some embedding
3. Incorrectly conclude C = P = NP

Showing two classes both embed in C does not mean C = P = NP.

## Formal Verification Summary

Our formalizations establish:
- ✅ Theorem 4.2 (∼P closed under e-reductions) — formally proved
- ✅ Theorem 5.2 (∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT) — axiomatized as valid
- ✅ Forward direction of Theorem 6.1 — formally proved
- ❌ Backward direction of Theorem 6.1 — formally blocked (cannot prove x = y)
- ❌ Theorem 5.3 (∼P = NP) — not formalizable (type mismatch)
- ❌ Theorem 6.2 (∼P = P) — not formalizable (type mismatch)
- ❌ Theorem 6.3 (P = NP) — not derivable

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) — Full text of the original paper
- [`../proof/README.md`](../proof/README.md) — Forward proof attempt
