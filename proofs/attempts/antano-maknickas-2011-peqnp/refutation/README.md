# Refutation: Maknickas (2011)

This directory contains formal demonstrations of why Maknickas's proof fails.

## Contents

- `lean/MaknickasRefutation.lean` — Lean 4 refutation
- `rocq/MaknickasRefutation.v` — Rocq refutation

## The Core Errors

### Error 1: LP Relaxation Gap (Primary Error)

**The fundamental problem**: The paper transforms k-SAT into a linear program,
but the LP does not faithfully encode Boolean satisfiability.

**Concretely**, for the clause `(X₁ ∨ X₂ ∨ X₃)`:
- **Boolean requirement**: At least ONE of X₁, X₂, X₃ must be TRUE
- **LP constraint**: `X₁ + X₂ + X₃ ≤ 3` with `Xᵢ ≥ 0`

The LP constraint is satisfied by `X₁ = X₂ = X₃ = 1`, but after applying the
recovery function `floor_mod2(1) = false`, all three literals become FALSE —
violating the original clause!

**Formal consequence**: The Rocq proof `bad_recovery_fails_on_clause3` shows
that the LP solution `(1, 1, 1)` is LP-feasible but the recovered Boolean
assignment does NOT satisfy the clause.

### Error 2: Negation is Completely Ignored

The LP constraint for a k-clause treats positive and negative literals identically:
```
clause_sum([Pos n]) = X_n
clause_sum([Neg n]) = X_n  ← same!
```

This means the LP for `X₁ ∧ ¬X₁` (trivially unsatisfiable) has the same
constraints as the LP for `X₁ ∧ X₁` (satisfiable). The encoding loses all
information about which variables are negated.

**Formal consequence**: `negation_information_lost` proves that the LP constraints
for `[Pos n]` and `[Neg n]` are logically equivalent. The proof `contradictory_lp_feasible`
shows `X₁ ∧ ¬X₁` is LP-feasible, yet `contradictory_is_unsat` proves it is Boolean
unsatisfiable.

### Error 3: Problem Type Mismatch

The paper converts a **decision problem** (does a satisfying assignment exist?) into
an **optimization problem** (maximize some LP objective). These are fundamentally
different problems:

| Aspect | Boolean SAT | LP Optimization |
|--------|-------------|-----------------|
| Variables | `{0, 1}` | `ℝ, Xi ≥ 0` |
| Goal | Find ANY satisfying assignment | Maximize objective function |
| Feasibility | Boolean conjunction/disjunction | Linear inequalities |

**Formal consequence**: `problem_type_mismatch` proves that there exists a formula
(the contradictory formula `X₁ ∧ ¬X₁`) that is LP-feasible but not Boolean-satisfiable.
Therefore LP feasibility does NOT imply satisfiability.

### Error 4: Unproven Recovery Soundness

The most critical omission: the paper **never proves** that the recovery function
`X̃ᵢ = ⌊Xᵢ⌋ (mod 2)` converts LP solutions into valid Boolean SAT solutions.

This claim would need to be proven, but it is in fact **false**, as demonstrated
by the counterexample in Error 1.

**Formal consequence**: `paper_main_claim_is_false` proves that the key property
the paper relies on is not only unproven but provably false.

## Concrete Counterexample

**Formula**: `F = (X₁ ∨ X₂ ∨ X₃)` — clearly satisfiable (e.g., `X₁ = true`)

**LP solution**: `X₁ = X₂ = X₃ = 1.0`

**LP feasibility check**: `1 + 1 + 1 = 3 ≤ 3` ✓ and each `Xᵢ = 1 ≥ 0` ✓

**Recovery**: `floor_mod2(1.0) = ⌊1.0⌋ mod 2 = 1 mod 2 = 1 ≠ 0` → `false`

**Result**: All three variables recover to `false`, making the clause `false ∨ false ∨ false = false`

**Conclusion**: The LP found a "solution" that, after recovery, **violates** the original clause!

## Why LP Relaxation Cannot Solve NP-Complete Problems

LP relaxation is a well-known technique in approximation algorithms. It **intentionally**
relaxes integer constraints to real numbers to get a tractable (polynomial-time) problem.
However:

1. The LP optimal solution is generally **fractional**, not integer
2. **Rounding** fractional solutions to integers (or Boolean values) does not preserve optimality or feasibility
3. The **integrality gap** between LP optimal and integer optimal can be arbitrarily large
4. For NP-complete problems, any polynomial-time recovery must fail unless P = NP

The recovery function `floor_mod2` is one specific rounding scheme, but no rounding
scheme can correctly solve NP-complete problems in polynomial time (unless P = NP).

## Status of Formalizations

| Component | Lean 4 | Rocq |
|-----------|--------|------|
| LP feasibility of bad solution | `axiom` (arithmetic) | Proved |
| Recovery fails on bad solution | `axiom` (arithmetic) | Proved |
| Negation information lost | `theorem` | `theorem` |
| Unsatisfiable formula is LP-feasible | `theorem` | `theorem` |
| Problem type mismatch | `theorem` | `theorem` |
| Main claim is false | `theorem` | `theorem` |

The Rocq arithmetic steps that rely on `Int_part` computations for specific real values
are proved using `Zfloor_ind`. The Lean 4 versions use `axiom` for these arithmetic steps
since Lean 4 without Mathlib requires more infrastructure for real number floor computations.

## See Also

- [`../README.md`](../README.md) — Overview of the attempt with full error analysis
- [`../ORIGINAL.md`](../ORIGINAL.md) — Markdown reconstruction of the original paper
- [`../proof/README.md`](../proof/README.md) — Forward proof formalization
