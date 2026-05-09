# Forward Proof Formalization: Maknickas (2011)

This directory contains formal proof attempts following Maknickas's argument as faithfully as possible.

## Contents

- `lean/MaknickasProof.lean` — Lean 4 formalization
- `rocq/MaknickasProof.v` — Rocq formalization

## What These Formalizations Capture

The formalizations follow the paper's argument step by step:

### Section 2: Multi-nary Logic Analytic Formulas

The paper defines:
```
gₙᵏ(a) = ⌊a⌋ + k (mod n)
```

**LEMMA 1**: `g₂⁰(a)` is the identity and `g₂¹(a)` is negation for Boolean values.
- **Status**: Proved in Rocq for specific values 0 and 1.

**LEMMA 2**: `gₙᵏ(a*b)` generates all two-variable Boolean functions.
- **Status**: `Axiom`/`sorry` — the paper's claim is imprecise about the product encoding.

### Section 3: Reduction of k-SAT to LP

The paper proposes to solve k-SAT by:
1. Relaxing Boolean variables `Xᵢ ∈ {0,1}` to real variables `Xᵢ ≥ 0`
2. For each k-clause `(X_{j} ∨ X_{j+1} ∨ ... ∨ X_{j+k-1})`, add constraint:
   ```
   X_j + X_{j+1} + ... + X_{j+k-1} ≤ k,   X_i ≥ 0
   ```
3. Maximize `βₖ(X₁, ..., Xₙ)` subject to these constraints

**Note**: The encoding ignores negation — `¬Xᵢ` and `Xᵢ` are treated identically in the sum.

**Theorem 5**: This LP formulation is well-defined (transformation is straightforward).
- **Status**: Proved (trivially — LP uses same clause structure).

**Theorem 6**: LP can be solved in O(n^3.5) by Karmarkar's algorithm.
- **Status**: Proved — LP is indeed polynomial time (this part of the paper is correct).

### Section 4: Recovering the Boolean Solution

After solving the LP, the paper proposes:
```
X̃ᵢ = ⌊Xᵢ⌋ (mod 2)
```

This is formalized as `floor_mod2(r) = (⌊r⌋ mod 2 = 0)`.

### Section 5: Main Claim (The Fatal Flaw)

The paper claims: "If LP is feasible for formula `f`, then `recover_assignment` gives a satisfying Boolean assignment."

**Status**: `Axiom`/`sorry` — This is the critical unproven step. It is marked as an axiom because **it is false**. See `../refutation/` for counterexamples.

The conditional theorem `kSAT_in_P_if_claim_holds` shows that IF the main claim were true, k-SAT would be in P. But the main claim is false.

## Where the Formalizations Stop

The formalizations use `sorry` (Lean 4) and `Admitted` (Rocq) at:

1. **Main Claim (Section 5)**: `maknickas_main_claim` — LP feasibility does NOT imply the recovered Boolean assignment satisfies the formula. This is the core error.

2. **Lemma 2**: The two-variable generation claim is imprecise in the paper. The paper uses products `a*b` but the encoding is unclear.

## The Core Error

The paper never proves that `recover_assignment` (applying floor then mod 2) to the LP solution gives a valid SAT solution. This is the fundamental gap:

- LP finds a solution in `ℝⁿ` (real-valued)
- The recovery function converts to `{0,1}ⁿ` (Boolean)
- **Nothing guarantees** the recovered Boolean assignment satisfies the original clauses

See `../refutation/` for a concrete counterexample showing this fails.

## See Also

- [`../ORIGINAL.md`](../ORIGINAL.md) — Markdown reconstruction of the paper
- [`../ORIGINAL.pdf`](../ORIGINAL.pdf) — Original paper PDF
- [`../refutation/README.md`](../refutation/README.md) — Explanation of why the proof fails
- [`../README.md`](../README.md) — Overview of the attempt
