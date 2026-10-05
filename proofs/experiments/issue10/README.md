# Issue #10: the Williams route to `NP ⊈ P`

Issue #10 asks for a proof attempt of `NP ⊈ P`. This is `P ≠ NP` stated as
non-containment. The current shared statement `Complexity.PNotEqualsNP` is
literally `¬ ∀ L, InNP L → InP L`. Because `P ⊆ NP` is proved
(`Complexity.pSubsetNP`), it is equivalent to the classes differing
(`npNotSubsetP_iff_classes_differ`).

The paired files [`lean/NPNotSubsetP.lean`](lean/NPNotSubsetP.lean) and
[`rocq/NPNotSubsetP.v`](rocq/NPNotSubsetP.v) use the same theorem names.
They are built on the shared `Complexity`, `Issue532.Machines` and
`Issue532.Circuits` modules and on Idea 41
(`proofs/experiments/issue532/lean/Idea41.lean`,
`proofs/experiments/issue532/ideas/Idea41.md`). Idea 41 develops Williams'
algorithm-to-lower-bound direction.

**`NP ⊈ P` is not proved here.** Known theorems are explicit hypotheses. There
are no axioms, `sorry` or `Admitted`.

## Reproducing the defects in PR #43

| Defect in PR #43 | Reproduction or fix |
| --- | --- |
| The first `WilliamsFramework.lean` did not compile: `Set` is undefined without Mathlib, `⟨5, by simp⟩` cannot prove the size bounds, and `P`, `NP`, `NEXP`, `CircuitSAT` and `circular_dependency_barrier` were `sorry` | PR #619 replaced it with regression checks. This directory builds with the pinned `leanprover/lean4:v4.34.1` and `rocq/rocq-prover:9.0`. |
| `size`, `depth` and `compute` were independent fields, so any function was a "small ACC⁰ circuit" | `legacy_every_function_small`. Shared circuits are gate lists: the size is `C.length` and the semantics is `output x C`. |
| The running time was a free label, so any solver could claim zero cost | `legacy_zero_cost_is_fast`. Shared costs count `Run` steps of a finite-table machine. `run_pos` proves every run takes at least one step. `no_one_step_circuitSAT` proves that no machine decides circuit satisfiability in one step. |
| The bound `2^n - n^δ` was meant as `2^(n - n^δ)`, with `δ : Nat` | `legacy_bound_misread` evaluates both. `legacy_exponent_collapses` shows that `2^(n - n^δ) = 1` for every natural `δ ≥ 1`. `legacy_bound_misses_budget` shows that `2^n - n^δ` breaks the Williams budget `t·(n+1) ≤ 2^n` at arbitrarily large `n`. |
| Malformed circuits were not excluded | `malformed_forward_wire` and `malformed_no_inputs`. `malformed_rejected` gives a malformed circuit that outputs `true` and is rejected by `CircuitSAT`. |
| `fast_PPoly_SAT_implies_P_neq_NP` took `NP ⊄ P/poly` as a hypothesis, closed it with the axiom `NP_not_subset_PPoly_implies_P_neq_NP`, and never used the algorithm | `npNotSubsetP_of_not_npSubsetPPoly` states the real bridge with `PSubsetPPoly` explicit. |
| Williams' method yields `NEXP ⊄ P/poly`, not `NP ⊄ P/poly` | `williams_nexp_lower_bound` states the actual conclusion. `nexp_lower_bound_of_pEqualsNP` shows that `P = NP` yields the same conclusion under the same theorems, so on its own it does not separate P from NP. |
| The axioms `williams_main_theorem`, `NP_not_subset_PPoly_implies_P_neq_NP`, `PPoly_SAT_is_hard`, `williams_2011_result` and the nonexistence axiom `we_dont_have_fast_TC0_SAT` | Removed. The known theorems are explicit hypotheses (`NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup`, `PSubsetPPoly`, `CircuitSATInNP`). The open obligation is the definition `FastCircuitSAT`, not an axiom. |
| The enumeration diagonal (see below) | `constant_circuit_agrees` and `no_bit_differs_from_all_circuits`. |
| The circularity claim (see below) | `williams_budget_not_polynomial`. |

## Relation to the Williams write-up

[`p_not_equal_np_proof_attempt.md`](../p_not_equal_np_proof_attempt.md), as
corrected in PR #619, explains Williams' theorem with its real quantifiers.
The theorem is formalized as `FastCircuitSAT` and `williams_method` in Idea 41.
PR #619 also added the zero-cost and malformed-circuit regressions in
[`WilliamsFramework.lean`](../WilliamsFramework.lean) and
[`WilliamsFramework.v`](../WilliamsFramework.v).

This directory adds three things:

* the issue #10 target `NP ⊈ P`;
* formal counterparts of the write-up's informal refutations;
* stronger negative tests: one-step machines, and circuits without inputs.

## Formal refutations

### The enumeration diagonal

PR #43's original write-up enumerated "all circuits of size `≤ n^c`" (polynomially
many) and output a bit differing from all of them on the input `x`. Two
things are wrong:

1. There are `2^{Θ(n^c log n)}` such circuits, not polynomially many
   (compare the counting in `Issue532.Circuits.shannon_circuits`).
2. No bit differs from every circuit on a fixed input. For every `x` of
   positive length and every bit `b`, a well-formed three-gate constant
   circuit outputs `b` (`constant_circuit_agrees`). A diagonal must differ
   from each circuit on *some* input, which is why the hierarchy theorem is
   used instead.

### The circularity claim

PR #43's original write-up claimed that a fast `P/poly`-SAT algorithm would solve an
NP-complete problem efficiently, so the route is circular. Williams' budget
is `2^n / n^{ω(1)}`, and `williams_budget_not_polynomial` proves that
`2^n / (n+1)^c` is not polynomially bounded. A `FastCircuitSAT` machine may
therefore take superpolynomial time, and meeting the obligation does not
presuppose `P = NP`. The converse is proved: a polynomial-time `CircuitSAT`
decider meets it (`fastCircuitSAT_of_inP`).

The real limitation is different. Williams' conclusion is about `NEXP`. The
route reaches `NP ⊈ P` only by refuting `FastCircuitSAT` itself
(`npNotSubsetP_of_not_fastCircuitSAT`, given `CircuitSATInNP`). That is a
lower bound on circuit-satisfiability algorithms, which is at least as hard
as the original problem.

### Circuit classes

PR #43's original files claimed a strict ladder `ACC⁰ ⊊ TC⁰ ⊊ … ⊊ P/poly`.
The known facts are narrower. `AC⁰ ⊊ ACC⁰`, because parity is outside `AC⁰`
(Furst–Saxe–Sipser 1984; Ajtai 1983). Also `ACC⁰ ⊆ TC⁰ ⊆ NC¹ ⊆ P/poly`.
Whether `ACC⁰ ⊊ TC⁰` or `TC⁰ ⊊ NC¹` is open. Williams' method has given
`NEXP ⊄ ACC⁰` (Williams, CCC 2011 / J. ACM 2014) and `NQP ⊄ ACC⁰`
(Murray–Williams, STOC 2018). `NEXP ⊄ TC⁰` and `NEXP ⊄ P/poly` are open. None
of these is formalized here.

## Verified scope

| Claim | Lean and Rocq name |
| --- | --- |
| `NP ⊈ P` is `PNotEqualsNP`, and it is equivalent to `P` and `NP` differing | `npNotSubsetP_iff_pNotEqualsNP`, `npNotSubsetP_iff_classes_differ` |
| A witness gives `NP ⊈ P`; with excluded middle, the converse holds | `npNotSubsetP_of_witness`, `witness_of_npNotSubsetP` |
| PR #43 legacy defects | `legacy_every_function_small`, `legacy_zero_cost_is_fast`, `legacy_bound_misread`, `legacy_exponent_collapses`, `legacy_bound_misses_budget` |
| Zero-cost and constant-time runs are impossible | `run_pos`, `step_of_run_one`, `step_halt_congr`, `no_one_step_circuitSAT` |
| Malformed circuits are rejected | `malformed_forward_wire`, `malformed_no_inputs`, `malformed_rejected` |
| Well-formed test circuits | `wf_oneTrue`, `wf_oneFalse`, `satisfiable_oneTrue`, `unsatisfiable_oneFalse` |
| The Williams budget is superpolynomial | `williams_budget_not_polynomial` |
| The enumeration diagonal fails | `constant_circuit_agrees`, `no_bit_differs_from_all_circuits` |
| The corrected bridges | `npNotSubsetP_of_not_npSubsetPPoly`, `williams_nexp_lower_bound`, `nexp_lower_bound_of_pEqualsNP`, `npNotSubsetP_of_not_fastCircuitSAT` |
| Certificate-length half of `CircuitSATInNP` | `satisfying_input_within_certBound` |

The Rocq `Legacy.Circuit` stores `compute` on `nat -> bool` instead of
`Fin n → Bool`; the defect it reproduces is the same.

## Next ingredient to discharge

As in the write-up, the premise of the route to `NP ⊈ P` is **`CircuitSATInNP`**, the
circuit-evaluating verifier. `satisfying_input_within_certBound` proves that
the certificate fits the linear bound `1·(|w|+1)`. What remains is a paired
`Complexity.Machine` with the following properties:

1. It decodes `encNat n` and the gate list `encList encGate C`.
2. It checks `WF n C` and that the certificate length is `n`.
3. It evaluates `C` gate by gate.
4. It halts within a polynomial number of `Run` steps.

The paired `Issue567.CircuitSyntax`/`CircuitSyntax` modules now implement
recognition of the exact encoding grammar by a six-state machine. They prove
termination on all paired inputs in exactly `|x| + 1` steps. This discharges
syntax recognition only; input counts and gate indices are not returned as
decoded data, and wire bounds, certificate length and NAND evaluation remain
unchecked by that machine. `circuitSATInNP_of_verifier_run` packages membership
once the full evaluator's bounded run theorem is supplied as an explicit
hypothesis. The unconditional target still fails in
`python3 experiments/issue625/check_membership.py`, so the `mem` arguments
remain necessary. See [the investigation](../../../experiments/issue625/README.md).

`Issue532.SATVerifier` is the model for such a proof. After that, the next
known theorem in Williams' chain is `LazyDiagonalSimulation` (the universal
nondeterministic simulation behind `NTimeHierarchy`). Neither ingredient
touches the open part, `FastCircuitSAT` or its refutation.

Rocq does not change this assessment. The Rocq twin checks the same
statements. The obstacle is mathematical, not a proof-assistant limitation.

## Verification

Run from the repository root:

```sh
lake build proofs.experiments.issue10.lean.NPNotSubsetP
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Circuits.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea16.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea41.v
rocq compile -Q . '' proofs/experiments/issue10/rocq/NPNotSubsetP.v
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The conclusions are listed in `scripts/proof_status.json`. The prover queries
there report every transitive assumption. A clean report does not discharge
the explicit hypotheses `CircuitSATInNP`, `PSubsetPPoly`, `NTimeHierarchy`,
`EasyWitnessLemma` and `WilliamsSpeedup`, nor the open `FastCircuitSAT`.
