# Issue 638: ETH, SETH and the October 2026 AI-lab claims

On 26–27 October 2026 OpenAI and Anthropic each published a Lean development
claiming a deterministic algorithm that decides (and counts) k-SAT in time
`2^{O_k(n · polyloglog n / √log n)}`. If correct, it refutes the
**Exponential Time Hypothesis** (ETH) and the **Strong ETH** (SETH). The case
study [`docs/case-studies/issue-638`](../../../docs/case-studies/issue-638/README.md)
covers sources, timeline and verdicts. This directory has the part that is
proved **in this repository**, in both Lean and Rocq, over the shared machine
model `Complexity.Machine` / `Complexity.Run`.

This directory does **not** re-prove the labs' algorithms. That is the job of
[`external-lean-reverification.yml`](../../../.github/workflows/external-lean-reverification.yml),
which rebuilds them on GitHub runners. Their results enter here only as the
named hypotheses `SubexpKSAT` / `SubexpAllK`. Nothing here claims `P = NP` or
`P ≠ NP`.

## Definitions (`lean/ETH.lean`, `rocq/ETH.v`)

| Name | Meaning |
|---|---|
| `Width k φ` | every clause of `φ` has at most `k` literals |
| `DecidesKSATWithin k m T` | on every width-`k` CNF `φ`, `m` started on `encodeCNF φ` halts within `T (numVars φ) |encodeCNF φ|` steps with answer `true ↔ Satisfiable φ` |
| `expTime c a d n len` | `c · 2^{⌊a·n/d⌋} · (len+1)^c`, i.e. `O*(2^{(a/d)n})` |
| `KSATExpTime k a d` | some machine and constant `c` decide k-SAT within `expTime c a d` |
| `ETH` | `∃ d > 0, ¬ KSATExpTime 3 1 d` (3-SAT is not in `O*(2^{n/d})`) |
| `SETH` | `∀ d > 0, ∃ k, ¬ KSATExpTime k (d−1) d` (no `O*(2^{(1−1/d)n})` for all k) |
| `SubexpKSAT k` | `∀ d > 0, KSATExpTime k 1 d`: the shape of the labs' claims |
| `SubexpAllK` | `∀ k, SubexpKSAT k` |
| `logBudget n` | `2^{⌊n / (⌊log₂ n⌋ + 1)⌋}`: a superpolynomial, subexponential budget |

The time bound is polynomial in the encoded length `|x|` and exponential only
in the number of variables `n`. This is the usual `O*` convention of
Impagliazzo–Paturi (2001). Because `numVars φ ≤ |encodeCNF φ|`, `KSATExpTime`
with `a = 0` is a polynomial-time bound.

## Certified results

All 13 theorems are listed, in both Lean and Rocq, in
[`scripts/proof_status.json`](../../../scripts/proof_status.json) and are checked
in CI by `scripts/check_proof_status.py`. None has a theorem hypothesis that is
not displayed in its statement.

| Theorem | Statement | Lean axioms | Rocq axioms |
|---|---|---|---|
| `pNotEqualsNP_of_eth` | `ETH → PNotEqualsNP` | propext, Classical.choice, Quot.sound | none |
| `pNotEqualsNP_of_seth` | `SETH → PNotEqualsNP` | propext, Classical.choice, Quot.sound | none |
| `not_eth_of_pEqualsNP` | `PEqualsNP → ¬ ETH` | propext, Classical.choice, Quot.sound | none |
| `not_seth_of_pEqualsNP` | `PEqualsNP → ¬ SETH` | propext, Classical.choice, Quot.sound | none |
| `eth_iff_not_subexp3` | `ETH ↔ ¬ SubexpKSAT 3` | propext, Classical.choice, Quot.sound | `Classical_Prop.classic` |
| `not_seth_of_subexpAllK` | `SubexpAllK → ¬ SETH` | propext | none |
| `ksatExpTime_exp_mono` | a smaller exponent `a/d ≤ a'/d'` gives the larger one | propext | none |
| `subexpKSAT_of_logBudget` | a k-SAT decider within `c · logBudget n · (|x|+1)^c` gives `SubexpKSAT k` | propext, Quot.sound | none |
| `logBudget_not_polynomial` | `¬ PolynomiallyBounded logBudget` | propext, Classical.choice, Quot.sound | none |
| `logBudget_gap` | `logBudget ≤ C_d · 2^{n/d}` for every `d > 0`, and `logBudget` is not polynomial | propext, Classical.choice, Quot.sound | none |
| `swap_eq_id_sub_singlet` | on two bits, `SWAP = I − 2·singlet` (integer 4×4 matrices) | none | none |
| `singlet_sq` | `(2·singlet)² = 2·(2·singlet)` | propext | none |
| `swap_sq` | `SWAP² = I` | propext | none |

The Lean axiom lists are reproduced by
[`experiments/issue638/PrintAxioms.lean`](../../../experiments/issue638/PrintAxioms.lean)
([output](../../../experiments/issue638/results/print_axioms.txt)). Helper lemmas
such as `ksatExpTime_of_inP_sat`, `not_eth_of_subexp3`, `not_eth_of_logBudget`,
`not_seth_of_logBudget`, `ksatExpTime_width_mono` and `subexpKSAT_width_mono`
are proved in both files but are not separately listed.

## What the results say

1. **ETH ⇒ P ≠ NP and SETH ⇒ P ≠ NP** (`pNotEqualsNP_of_eth`,
   `pNotEqualsNP_of_seth`). The proof uses the repository's proved
   `SATVerifier.satInNP` and `Idea41.poly_le_two_pow`. If `P = NP`, then SAT is
   in P, and a polynomial bound is `O*(2^{δn})` for every δ. No Cook–Levin
   hypothesis is needed. So the hypotheses are **strictly stronger** than
   `P ≠ NP`, which is why papers that assume them prove more.
2. **A subexponential k-SAT algorithm refutes ETH, and for every k also SETH**
   (`eth_iff_not_subexp3`, `not_seth_of_subexpAllK`). This is the logical
   form of the October 2026 claims, stated over our machine model.
3. **Refuting ETH does not give P = NP**. `logBudget_gap` shows that a budget
   can be below every `2^{δn}` and still not be polynomial. The labs' bounds
   `2^{C·n·loglog n/√log n}` are above `logBudget` for large n. Even a fully
   verified ETH refutation therefore leaves `P vs NP` open. `P ≠ NP` loses one
   of its *stronger* conditional supports (ETH), and nothing more.
4. **The algebraic seed of Anthropic's key idea** (`swap_eq_id_sub_singlet`).
   This is the one-bit identity only. The tensor-rank bound `≤ 12^λ` that the
   upstream README builds on it is checked **numerically** for `λ ≤ 4` by
   [`experiments/issue638/swap_singlet_ranks.py`](../../../experiments/issue638/swap_singlet_ranks.py)
   ([output](../../../experiments/issue638/results/swap_singlet_ranks.txt)). It is
   not proved here.

## Open obligations

* **Model transfer (planned issue P8).** Moving the labs' theorems from Mathlib's
  `Turing.FinTM2` (Anthropic) or OpenAI's `PrimitiveMachine` to
  `Complexity.Machine` needs a simulation theorem with a polynomial time
  overhead, plus an encoding translation from their CNF encodings to
  `encodeCNF`. The repository has no Mathlib dependency, so the labs' Lean
  code cannot be imported directly. Until this is done, `SubexpKSAT 3` is
  **not** a theorem of this repository. It is a named hypothesis.
* **Sparsification (planned issue P9).** SETH ⇒ ETH needs the
  Impagliazzo–Paturi–Zane sparsification lemma. It is not formalized here.
  Anthropic's `eth/` development contains a sparsification library, which is
  the closest existing component.
* The rank bound `≤ 12^λ` for all λ (see item 4).

## Reproduce

Toolchains: Lean `v4.34.1` (`lean-toolchain`) and Rocq 9.0 (CI image).

```sh
lake build proofs.experiments.issue638.lean.ETH
lake env lean experiments/issue638/PrintAxioms.lean
for f in proofs/complexity/rocq/Complexity.v \
         proofs/experiments/issue532/rocq/Machines.v \
         proofs/experiments/issue532/rocq/SATVerifier.v \
         proofs/experiments/issue532/rocq/Circuits.v \
         proofs/experiments/issue532/rocq/Idea16.v \
         proofs/experiments/issue532/rocq/Idea41.v \
         proofs/experiments/issue638/rocq/ETH.v; do
  rocq compile -Q . '' "$f"
done
python3 experiments/issue638/check_issue638_status.py   # issue #638 entries only
python3 scripts/check_proof_status.py                   # full audit (CI)
python3 -I experiments/issue638/swap_singlet_ranks.py 4
```

The heavy external rebuilds (the Anthropic and OpenAI projects with their
Mathlib versions) run only in CI, not locally. See the case study for their
status.
