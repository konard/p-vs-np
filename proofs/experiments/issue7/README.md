# Issue #7: the clocked-SAT sentence in the shared model

Issue #7 asked to "try prove P vs NP is undecidable". The corrected target is
**independence from a fixed object theory** `T = ZFC`:

```text
Ind_T(φ) := ¬Pr_T(⌜φ⌝) ∧ ¬Pr_T(⌜¬φ⌝)
```

Here `φ` is the ZFC translation of the clocked-SAT sentence. The
[research roadmap](../../../PROVING_P_VS_NP_UNDECIDABILITY.md) sets the first
concrete task: write paired Lean and Rocq statements of the clocked-SAT
equivalence, keep `SATHard` explicit, and prove a clock lemma with no new
admissions. This directory completes that task.

The paired files [`lean/ClockedSAT.lean`](lean/ClockedSAT.lean) and
[`rocq/ClockedSAT.v`](rocq/ClockedSAT.v) use the same theorem names. They are
built on the shared `Complexity`, `Issue532.Machines` and
`Issue532.SATVerifier` modules. They define no new SAT language, verifier or
machine model.

**Nothing here proves P = NP, P ≠ NP, or anything about ZFC.** Independence
of P vs NP, and the provability of either side, stay open. The Cook–Levin
hardness half, `SATHard`, is an explicit premise and is still unproved in the
shared model. There are no axioms, `sorry` or `Admitted`.

## The two forms

`clockCheck m p x` is the computable matrix `R(e,k,x)`. It runs machine `m` on
input `x` for at most `p(|x|)` steps, and it returns `true` exactly when `m`
halts within that clock with the SAT answer. The two forms are:

```text
ClockedSAT       :=  ∃ m p, ∀ x, clockCheck m p x = true      (Σ⁰₂ form)
¬ ClockedSAT     ⇔   ∀ m p, ∃ x, clockCheck m p x = false     (Π⁰₂ form)
```

In the Π⁰₂ form, the **same** language SAT defeats every machine and clock.
`per_machine_form_holds` proves that the other quantifier order, "every
clocked machine fails to decide *some* NP language", holds with no hypothesis.
Every machine gives the wrong answer on the empty input for one of the two
constant languages, and both constant languages are in P. That form cannot
express P ≠ NP.

## Verified scope

| Claim | Lean `Issue7.ClockedSAT.*` and Rocq `ClockedSAT.*` |
| --- | --- |
| Clock lemma: the fuel-bounded interpreter `runFor` returns exactly the `Run`s that fit in the fuel | `runFor_iff` |
| The Boolean matrix `clockCheck` decides the `Prop` matrix inside `DecidesWithin` | `clockCheck_iff` |
| No premise: the Σ⁰₂ form is `PolyDec SAT`, which is `InP SAT` | `clockedSAT_iff_polyDec`, `clockedSAT_iff_inP_sat` |
| No premise: `PEqualsNP` gives the Σ⁰₂ form, using the proved `satInNP` | `clockedSAT_of_pEqualsNP` |
| Given `SATHard`: the Σ⁰₂ form gives `PEqualsNP`, and the two are equivalent | `pEqualsNP_of_clockedSAT`, `clockedSAT_iff_pEqualsNP` |
| `¬ClockedSAT` is the Π⁰₂ form | `not_clockedSAT_iff` |
| No premise: the Π⁰₂ form gives `PNotEqualsNP`. The converse needs `SATHard` | `pNotEqualsNP_of_pi2`, `pi2_of_pNotEqualsNP` |
| The wrong quantifier order holds with no premise | `per_machine_form_holds` |
| Non-vacuity: `clockCheck` holds for some instances and fails for others | `clockCheck_rejectAll_empty_clause`, `clockCheck_rejectAll_empty_cnf`, `rejectAll_defeated`, `clockCheck_zero_clock` |

`rejectAll_defeated` is a Π⁰₂ instance for **one** machine: the empty table is
wrong on the satisfiable empty formula under every clock. It says nothing
about other machines.

Assumption audit, from `#print axioms` and `Print Assumptions`:

* Lean uses only `propext`, `Quot.sound` and, for the theorems that go
  through `satInNP` or the Π⁰₂ form, `Classical.choice`.
* In Rocq, every theorem is closed under the global context except the three
  Π⁰₂ theorems (`not_clockedSAT_iff`, `pNotEqualsNP_of_pi2`,
  `pi2_of_pNotEqualsNP`). These use `Classical_Prop.classic`, because turning
  `¬∃ m p, ∀ x, …` into `∀ m p, ∃ x, …` needs excluded middle.

## Can an automated proof settle the question?

The maintainer asked whether we can prove or disprove independence "exactly",
using an automated proof. The current evidence gives these answers.

* **The question has a definite answer, but there is no known way to reach
  it.** In classical logic, `Ind_T(φ)` is either true or false. No theorem
  gives an algorithm that decides it, or guarantees a proof of either answer
  in our metatheory.
* **To refute independence**, we need a genuine ZFC proof of `φ` or of `¬φ`.
  With `SATHard`, that is a proof of P = NP or of P ≠ NP. An automated proof
  search can enumerate candidate proofs and check them, but it may run
  forever: if `φ` is independent, no proof exists to find.
* **To prove independence**, we need a metatheorem that shows both
  `Con(ZFC + φ)` and `Con(ZFC + ¬φ)` under stated assumptions. Ordinary forcing
  over a transitive ground model preserves the truth of this arithmetic
  sentence, so an argument cannot use such a model and its forcing extension
  as the two models. Their invariance does not establish provability either.
  No such argument is known.
* **What automation does check** is each step that is finite and exact. This
  directory is such a step: the prover kernels check that the arithmetic
  sentence has the stated quantifier shape and matches `InP SAT` over the
  shared model.

## Next ingredients to discharge

These steps are checkable now and do not presuppose the open problem:

1. **`SATHard` in the shared model.** Cook–Levin is a known theorem. Proving
   it for `Complexity.Machine` removes the premise from
   `pEqualsNP_of_clockedSAT`, `clockedSAT_iff_pEqualsNP` and
   `pi2_of_pNotEqualsNP`.
2. **A coding of machines and clocks as natural numbers.** `ClockedSAT`
   quantifies over `Machine` and `Polynomial` values. The arithmetic sentence
   quantifies over codes `e` and `k`. A proved coding would state `ClockedSAT`
   as a Σ⁰₂ formula over `ℕ` with a primitive recursive matrix.
3. **The ZFC translation of `φ` and a proof predicate `Proof_T`.** Only with
   these can a theorem about `Ind_T(φ)` be stated. The
   [independence schema](../../p_vs_np_undecidable/README.md) still leaves its
   proof relation abstract.

## Verification

Run from the repository root:

```sh
lake build proofs.experiments.issue7.lean.ClockedSAT
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/SATVerifier.v
rocq compile -Q . '' proofs/experiments/issue7/rocq/ClockedSAT.v
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
python3 experiments/issue579/check_claims.py
```

The conclusions are listed in `scripts/proof_status.json`. A clean report does
not discharge the explicit premise `SATHard`, and it says nothing about ZFC
provability.
