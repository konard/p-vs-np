# Issue #8: the target `NP ⊆ P` and a verified DPLL solver

Issue #8 asked to "try prove P = NP". Its corrected target is **`NP ⊆ P`**.
The shared statement `Complexity.PEqualsNP` is literally
`∀ L, InNP L → InP L` (`npSubsetP_iff_pEqualsNP`). Because `P ⊆ NP` is proved
(`Complexity.pSubsetNP`), it is equivalent to the classes being equal
(`npSubsetP_iff_classes_equal`).

The paired files [`lean/NPSubsetP.lean`](lean/NPSubsetP.lean) and
[`rocq/NPSubsetP.v`](rocq/NPSubsetP.v) use the same theorem names. They are
built on the shared `Complexity`, `Issue532.Machines` and
`Issue532.SATVerifier` modules, on the issue #609 replacement for PR #41's
proof files ([`../issue609/`](../issue609/README.md)), and on Idea 41's
`poly_le_two_pow`.

**`NP ⊆ P` is not proved here.** The Cook–Levin hardness half, `SATHard`, is
an explicit premise. There are no axioms, `sorry` or `Admitted`.

## Reproducing the defects in PR #41

| Defect in PR #41 | Reproduction or fix |
| --- | --- |
| `PEqualsNPAttempt.lean` declared `axiom contradiction_from_separation : False`, so every statement in the file was provable, together with axioms for a hypothetical solver, its time bound and its correctness | The file is not in `main`. Issue #609 replaced it and `KnownBarriers.lean` with paired files that assert no axioms. This directory adds no axioms either; `scripts/proof_status.json` audits every conclusion. |
| The Python DPLL in `experiments/sat_solvers/dpll_basic.py` answered UNSAT for the satisfiable `(¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x1 ∨ ¬x3) ∧ (x1 ∨ ¬x2) ∧ (x1 ∨ x3)` (issue #610) | PR #616 fixed the Python solver. `issue610_satisfiable` and `issue610_sat` prove the formula satisfiable in the shared semantics, and `dpllSAT_issue610` checks that the verified solver accepts it. |
| No solver was connected to the shared SAT language, and no cost was stated | `dpll_correct` and `dpllSAT_eq_SAT` prove a DPLL search correct on every word. `dpllSAT_calls_le` bounds its calls. `candidate_of_dpll_machine` names what a polynomial-time machine for it would give. |
| The write-up and next-steps documents contained wrong citations and claims | They are replaced by the corrected [`np_subset_p_proof_attempt.md`](../np_subset_p_proof_attempt.md), which lists each correction. |

## The verified solver

`dpll k φ` is a functional DPLL search. It rejects a formula with an empty
clause, applies the first unit clause, and otherwise splits on the first
literal of the first clause. Each branch conditions its own copy of the
formula with `assign`, so no assignment trail has to be restored. This is the
state that the issue #610 bug corrupted. The fuel `k` bounds the variables
still present.

`dpllSAT w := dpll |w| (decode w)` uses the input length as fuel. This is
enough because `varsBelow_decode` bounds every variable of `decode w` by
`|w|`. The results are as follows:

* `dpll_correct`: if every variable of `φ` is in a list `S` with
  `|S| ≤ k`, then `dpll k φ = true` iff `φ` is satisfiable;
* `dpllSAT_eq_SAT`: `dpllSAT w = SAT w` for every word `w`, including words
  that are not well-formed encodings;
* `dpllSAT_empty_clause`: the encoding of `[[]]` is rejected. This is a
  non-vacuity check: a constant-`true` solver fails it, and a constant-`false`
  solver fails `dpllSAT_issue610`;
* `dpllSAT_calls_le`: `dpll` makes fewer than `2^(|w|+1)` calls, counting the
  short-circuit of `||`;
* `calls_bound_not_polynomial`: that bound is not polynomial.

`calls_bound_not_polynomial` is a statement about the proved **upper** bound.
It is not a lower bound on SAT, nor on this algorithm. The call count is also
not a count of `Run` steps of a `Complexity.Machine`.

## Verified scope

| Claim | Lean `Issue8.NPSubsetP.*` and Rocq `NPSubsetP.*` |
| --- | --- |
| `NP ⊆ P` is `PEqualsNP` and is equivalent to the classes being equal | `npSubsetP_iff_pEqualsNP`, `npSubsetP_iff_classes_equal` |
| Given `SATHard`, `NP ⊆ P` is equivalent to `SAT ∈ P` and to an issue #609 `Candidate` | `npSubsetP_iff_inP_sat`, `npSubsetP_iff_candidate` |
| The issue #610 formula is satisfiable and the solver accepts it | `issue610_sat`, `dpllSAT_issue610` |
| DPLL is correct for the shared SAT language | `dpll_correct`, `dpllSAT_eq_SAT` |
| Non-vacuity: an unsatisfiable instance is rejected | `dpllSAT_empty_clause` |
| Call bound, which is not polynomial | `dpllSAT_calls_le`, `calls_bound_not_polynomial` |
| A polynomial `Run` bound for `dpllSAT` gives a `Candidate`, and with `SATHard` gives `NP ⊆ P`. Conversely, `NP ⊆ P` gives such a machine without `SATHard` | `candidate_of_dpll_machine`, `npSubsetP_of_dpll_machine`, `dpll_machine_of_npSubsetP` |

## What blocks this attempt

`npSubsetP_of_dpll_machine` and `dpll_machine_of_npSubsetP` show that, given
`SATHard`, the remaining obligation is equivalent to the target: a
`Complexity.Machine` deciding `dpllSAT` (that is, SAT) within a polynomial
number of `Run` steps. Nothing else in the file is open.

* The only bound proved for DPLL is exponential. DPLL-style search without
  learning produces tree-like resolution refutations, which need exponential
  size on known families (for example the pigeonhole formulas; Haken 1985
  proves the lower bound even for general resolution). A different algorithm
  would be needed, not a better analysis of this one.
* The obligation cannot be met by a relativizing argument (Baker–Gill–Solovay
  1975), and any proof must also be consistent with every known conditional
  consequence of `P = NP`, for example the collapse of the polynomial
  hierarchy and the absence of one-way functions.

Rocq does not change this. The twin checks the same statements; the obstacle
is mathematical.

## Next ingredients to discharge

These steps are checkable now and do not presuppose the open problem:

1. **A `Run`-step cost for the solver.** Implement `dpll` as a
   `Complexity.Machine`, prove that it decides `dpllSAT`, and give an explicit
   `2^O(|w|)` bound on its `Run` steps. This would turn the call count into
   the machine cost that `DecidesWithin` measures, as
   `Issue532.SATVerifier` does for the verifier.
2. **`SATHard` in the shared model.** Cook–Levin is a known theorem.
   Proving it for `Complexity.Machine` removes the premise from
   `npSubsetP_iff_inP_sat`, `npSubsetP_iff_candidate` and
   `npSubsetP_of_dpll_machine`.
3. **An exponential lower bound for this `dpll`.** A family of unsatisfiable
   formulas on which `dpllCalls` is at least `2^(Ω(n))` would prove formally
   that this solver is not polynomial. That result is about one algorithm, not
   about SAT.

## Verification

Run from the repository root:

```sh
lake build proofs.experiments.issue8.lean.NPSubsetP
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/SATVerifier.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Circuits.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea41.v
rocq compile -Q . '' proofs/experiments/issue609/rocq/PEqualsNPAttempt.v
rocq compile -Q . '' proofs/experiments/issue8/rocq/NPSubsetP.v
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The conclusions are listed in `scripts/proof_status.json`. The prover queries
there report every transitive assumption. A clean report does not discharge
the explicit premise `SATHard`, nor the open polynomial `Run` bound.
