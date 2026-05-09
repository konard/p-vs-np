# Frank Vega (2015) - P = NP via equivalent-P

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

**Attempt ID**: 104
**Author**: Frank Vega
**Year**: 2015
**Claim**: P = NP
**Paper**: "Solution of P versus NP Problem"
**Source**: [HAL Archive hal-01161668](https://hal.science/hal-01161668)
**Woeginger's List**: Entry #104 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

In June 2015, Frank Vega introduced a new complexity class called **equivalent-P** (denoted ∼P), which has a close relation to the P versus NP question. The class ∼P contains languages of ordered pairs of instances where each instance belongs to a specific problem in P, such that the two instances share the same solution (certificate).

Vega's argument proceeds in four steps:
1. Define the complexity class ∼P (Definition 3.1)
2. Show ∼P is closed under e-reductions (Theorem 4.2)
3. Show that ∼P = NP (Theorem 5.3) via ∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT
4. Show that ∼P = P (Theorem 6.2) via ∼HORNSAT ∈ ∼P
5. Conclude P = NP (Theorem 6.3)

## The Critical Error

The proof contains a fundamental type error: ∼P is a class of **pair languages** (predicates on ordered pairs), while P and NP are classes of **single-string languages**. The statements "∼P = NP" and "∼P = P" are therefore type errors — they compare objects of incompatible types.

Even if we interpret these claims charitably (via diagonal embeddings), the argument shows only that P and NP both embed into ∼P, not that P = NP. Showing two sets both have subsets in a third set does not prove the two sets are equal.

A secondary error: the shared certificate condition in Definition 3.1 is vacuous for P problems (any certificate can be trivially accepted), which makes the definition degenerate.

## Formalization Goals

The formalizations in Lean 4 and Rocq:
1. Encode each definition and theorem from the paper
2. Prove what can be proved (Theorem 4.2, forward directions)
3. Use `sorry`/`Admitted` at steps that cannot be completed, with detailed comments explaining why

## Files

- [`ORIGINAL.pdf`](ORIGINAL.pdf) — Original paper from HAL Archive
- [`ORIGINAL.md`](ORIGINAL.md) — Markdown conversion of the paper
- [`proof/`](proof/) — Forward proof formalization (following Vega's argument)
  - [`proof/README.md`](proof/README.md) — Explanation of what compiles and what fails
  - [`proof/lean/VegaProof.lean`](proof/lean/VegaProof.lean) — Lean 4 formalization
  - [`proof/rocq/VegaProof.v`](proof/rocq/VegaProof.v) — Rocq formalization
- [`refutation/`](refutation/) — Formal demonstration of the errors
  - [`refutation/README.md`](refutation/README.md) — Explanation of each error
  - [`refutation/lean/VegaRefutation.lean`](refutation/lean/VegaRefutation.lean) — Lean 4 refutation
  - [`refutation/rocq/VegaRefutation.v`](refutation/rocq/VegaRefutation.v) — Rocq refutation

## Provable vs. Blocked Results

| Theorem | Status | Reason |
|---------|--------|--------|
| Theorem 4.2 (∼P closed under e-reductions) | ✅ Proved | Formal proof complete |
| Theorem 5.2 (∼ONE-IN-THREE 3SAT ≤∼ 3XOR-2SAT) | ✅ Axiomatized | Combinatorial argument valid |
| ∼ONE-IN-THREE 3SAT ∈ ∼P | ✅ Proved | Via Theorems 4.2 and 5.2 |
| Theorem 6.1 forward direction | ✅ Proved | (φ,φ) ∈ ∼HORNSAT → ∼P conditions |
| Theorem 6.1 backward direction | ❌ Blocked | Cannot prove x = y from vacuous certificate |
| Theorem 5.3 (∼P = NP) | ❌ Not formalizable | Type mismatch: PairLanguage ≠ Language |
| Theorem 6.2 (∼P = P) | ❌ Not formalizable | Type mismatch: PairLanguage ≠ Language |
| Theorem 6.3 (P = NP) | ❌ Not derivable | Conclusion requires fixing all above errors |

## References

- Frank Vega, "Solution of P versus NP Problem", HAL preprint hal-01161668, June 2015
- https://hal.science/hal-01161668
- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Status

- ✅ Paper analyzed and converted to markdown
- ✅ Original PDF archived
- ✅ Lean formalization: Complete (with documented sorry points)
- ✅ Rocq formalization: Complete (with documented Admitted points)
- ✅ Errors identified and formally documented

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Documentation](../../../P_VS_NP_TASK_DESCRIPTION.md)
