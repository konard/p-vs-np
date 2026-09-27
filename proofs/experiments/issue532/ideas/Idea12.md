# Idea 12 — Reduction verification

**Verdict:** Correct tool, insufficient alone (general theorem proved). Many-one reductions are exactly the right instrument for moving algorithms and hardness between problems, and this is proved in general in the repository's shared machine model: machine reductions (`PolyReduces`, a finite-table machine computing the map within a polynomial number of `Run` steps) form a preorder (`polyReduces_refl`, `polyReduces_trans`), P pulls back along them (`poly_decider_transfer`, the shared `inP_of_reduces`), and non-membership in P pushes forward (`hardness_transfer`, with the SAT instance `sat_hardness_transfer`); the hypothesis `¬ InP L` is satisfiable (`diag_hardness_transfer`). The same general theorems show why reductions cannot settle P vs NP by themselves: "reduce SAT to something in P" is equivalent to `InP SAT` (`sat_reduction_route_iff`) and gives P = NP only under the named hypothesis `SATHard`; they also catch the recurring "invalid reduction" error: constant maps are never reductions from a nontrivial language, a yes-to-yes check alone accepts such maps (`const_not_reduction`, `yes_preserving_not_sufficient`), and without cost bounds every language reduces to every nontrivial one (`reduces_to_any_nontrivial`), whereas with machine cost the diagonal language does not reduce to the easy language `firstBit` (`reduction_cost_essential`).

## 1. The idea at full strength

Many attempts in the repository (family 4 in
[`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)) have the shape:

1. Transform an NP-complete problem `L` (SAT, 3-colouring, TSP) into a
   problem `M` that the author can solve (a linear system, a graph problem
   in P, a physical process).
2. Solve `M` in polynomial time.
3. Conclude P = NP.

Or, for P ≠ NP: transform a problem into SAT, observe that SAT is hard, and
conclude that the problem is hard.

At full strength the idea is: *reductions are complete for the question*,
since P = NP iff SAT has a polynomial decider (Cook 1971; Levin 1973), and
any polynomial reduction from SAT to a problem in P settles it. The
dossier checks exactly what a reduction must satisfy and what it delivers.

## 2. Precise mathematical formulation

**Reductions.** `IsReduction f L M :≡ ∀ x, L x = M (f x)` for
`f : α → β`, `L : α → Bool`, `M : β → Bool`. `Nontrivial L` means `L` has a
yes-instance and a no-instance.

**Machine model.** The shared model of
`proofs/complexity/lean/Complexity.lean` and
`proofs/experiments/issue532/lean/Machines.lean`: languages are
`Word → Bool` with `Word = List Bool`; a machine is a finite instruction
table; `Run M c t b` counts steps. `InP L` means one machine decides `L` on
every word within one polynomial `c·(n+1)^d` (equivalently `PolyDec L`).

* `Computes m f p`: from `initial x`, machine `m` reaches, within
  `p(|x|)` steps, the state just past its table with the head at the left end
  and `f x` followed by blanks on the tape.
* `PolyReduces L L' :≡ ∃ m f p, Computes m f p ∧ ∀ x, L x = L' (f x)`.
  The output-size bound is not a separate field: it follows from the time
  bound (`computes_output_poly`, shared layer).
* Composition runs the concatenated table `appendMachine m m'`: the first
  table, then the second with every state shifted. The running times add.
* Known theorems appear only as the named hypotheses of the shared layer:
  `SATHard := NPHard SAT` and `SATInNP := InNP SAT` (Cook–Levin, not
  mechanised).

**Abstract schema (kept).** The earlier abstract model, where an `Algo α β`
is a pair `(run, time)` whose `time` is a declared field, is kept as a schema
under the names `PolyBoundedFor`, `PolyDeciderFor`, `PolyReductionFor` and
`poly_decider_transfer_for`, `poly_reduction_comp_for`,
`hardness_transfer_for`. It records the explicit constants
`(e + c(e+1)^d)(n+1)^(kd+k)`. It is not a statement about P:
`polyDeciderFor_every` proves that every language has a schema decider with
declared time `0`. `polyDeciderFor_of_inP` instantiates the schema with the
machine step count.

**Claims under test.** (a) A map that sends yes-instances to yes-instances
is a reduction. (b) "`M` reduces to SAT, so `M` is hard." (c) A polynomial
reduction from `L` to `M` plus a polynomial decider for `M` gives one for
`L`; and polynomial reductions compose.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `reduction_id` | The identity reduces every language to itself. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `reduction_comp` | Reductions compose. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `reduction_complement` | A reduction from `L` to `M` is also one from `¬L` to `¬M`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `const_reduction_iff` | A constant map `_ ↦ c` is a reduction iff `L x = M c` for all `x`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `const_not_reduction` | No constant map reduces a nontrivial language. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `trivial_target` | A reduction into a constant language forces the source to be constant. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `nontrivial_target` | The target of a reduction from a nontrivial language is nontrivial. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `decider_transfer` | A decider for `M` that is correct on the image of `f` gives a decider `g ∘ f` for `L`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `yes_preserving_not_sufficient` | For every nontrivial `L` and yes-instance `y` of `M`, the constant map to `y` sends yes to yes but is not a reduction. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `reduces_to_any_nontrivial` | Without cost bounds, every `L` reduces to every nontrivial `M`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `computes_id` | The empty table computes the identity in zero steps. | [Lean](../lean/Idea12.lean) | planned: `computes_id` |
| `computes_comp` | `Computes m f p → Computes m' g p' → ∃ B, Computes (appendMachine m m') (g ∘ f) B`. | [Lean](../lean/Idea12.lean) | planned: `computes_comp` |
| `polyReduces_refl` | `PolyReduces L L`. | [Lean](../lean/Idea12.lean) | planned: `polyReduces_refl` |
| `polyReduces_trans` | `PolyReduces L M → PolyReduces M N → PolyReduces L N` (machine reductions compose). | [Lean](../lean/Idea12.lean) | planned: `polyReduces_trans` |
| `polyReduces_complement` | `PolyReduces L L' → PolyReduces (complement L) (complement L')`. | [Lean](../lean/Idea12.lean) | planned: `polyReduces_complement` |
| `inP_of_reduces` | `PolyReduces L L' → InP L' → InP L` (shared layer). | [Machines.lean](../lean/Machines.lean) | shared `Machines.v` |
| `poly_decider_transfer` | `PolyReduces L L' → InP L' → InP L` (restated here). | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `hardness_transfer` | `PolyReduces L L' → ¬ InP L → ¬ InP L'`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `sat_hardness_transfer` | `PolyReduces SAT L' → ¬ InP SAT → ¬ InP L'`. | [Lean](../lean/Idea12.lean) | planned: `sat_hardness_transfer` |
| `diag_hardness_transfer` | `PolyReduces Diag L' → ¬ InP L'`: the hypothesis of `hardness_transfer` is satisfiable. | [Lean](../lean/Idea12.lean) | planned: `diag_hardness_transfer` |
| `firstBit_inP` | The language "first bit is 1" is decided in one step. | [Lean](../lean/Idea12.lean) | planned: `firstBit_inP` |
| `reduction_cost_essential` | `Diag` reduces to `firstBit` by an unrestricted map but `¬ PolyReduces Diag firstBit`. | [Lean](../lean/Idea12.lean) | planned: `reduction_cost_essential` |
| `sat_reduction_route_iff` | `(∃ M, PolyReduces SAT M ∧ InP M) ↔ InP SAT`. | [Lean](../lean/Idea12.lean) | planned: `sat_reduction_route_iff` |
| `pEqualsNP_of_sat_reduction_route` | `SATHard → (∃ M, PolyReduces SAT M ∧ InP M) → PEqualsNP`. | [Lean](../lean/Idea12.lean) | planned: `pEqualsNP_of_sat_reduction_route` |
| `npHard_of_reduces` | `SATHard → PolyReduces SAT M → NPHard M`. | [Lean](../lean/Idea12.lean) | planned: `npHard_of_reduces` |
| `poly_bound_compose` | `a ≤ e(n+1)^k` and `b ≤ c(a+1)^d` imply `b ≤ c(e+1)^d (n+1)^(kd)`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_sum_bound` | `e(n+1)^k + C(n+1)^(kd) ≤ (e+C)(n+1)^(kd+k)`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_decider_transfer_for` / `poly_decider_transfer` | Schema: a schema reduction and a schema decider give a schema decider, with explicit constants. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_reduction_comp_for` / `poly_reduction_comp` | Schema: schema reductions compose, with explicit constants. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `hardness_transfer_for` / `hardness_transfer` | Schema version of hardness transfer. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `polyDeciderFor_every` | Every language has a schema decider (declared time `0`): the schema alone is vacuous. | [Lean](../lean/Idea12.lean) | planned: `polyDeciderFor_every` |
| `polyDeciderFor_of_inP` | `InP L → PolyDeciderFor List.length L` (schema instantiated with the step count). | [Lean](../lean/Idea12.lean) | planned: `polyDeciderFor_of_inP` |

In Rocq, `reduction_id` and `reduction_comp` state the defining equations
directly (`∀ x, L x = L (id x)` and `∀ x, L x = N (g (f x))`), because the
section fixes distinct type variables; they are the same statements. The
Rocq file still contains the abstract cost model under the old names; porting
it to the shared Rocq machine layer, under the names marked "planned", is
pending. Where the current Rocq name differs, the first column gives both
(`Lean` / `Rocq`). Not machine-checked: the Cook–Levin theorem, which enters only as
the named hypothesis `SATHard`. No theorem in either file proves or refutes
P = NP.

## 4. Complete argument

**Basic algebra.** Composition: `L x = M (f x) = N (g (f x))`. Complement:
apply `!` to both sides. Nontriviality: images of a yes- and a no-instance
of `L` are a yes- and a no-instance of `M`. A reduction into a constant
language makes `L x = M (f x) = b` for all `x`.

**Constant and one-directional maps.** If `_ ↦ c` were a reduction from a
nontrivial `L`, then `true = L a = M c = L b = false`. The constant map to a
yes-instance of `M` sends every yes-instance of `L` to a yes-instance, so a
check of only one direction ("every satisfiable formula maps to a
solvable system") accepts it; `yes_preserving_not_sufficient` shows this
check is useless on *every* nontrivial source language. A valid reduction
needs both directions, `L x = true → M (f x) = true` and
`M (f x) = true → L x = true`.

**Reductions without cost bounds.** If `M` has a yes-instance `a` and a
no-instance `b`, then `x ↦ if L x then a else b` is a reduction from any
`L`. The map decides `L` itself. Hence "problem X reduces to SAT" proves
nothing about the difficulty of X, and every hardness statement needs a
bound on the reduction's cost.

**Machine reductions compose.** Let `m` compute `f` within `p` and `m'`
compute `g` within `p'`. The table `appendMachine m m'` first runs `m`
unchanged (`reaches_append`, shared layer): after `t₁ ≤ p(|x|)` steps it is in
state `|m|` with the head at the left end and `f x` followed by blanks on the
tape. This configuration agrees up to trailing blanks with the shifted
initial configuration of `m'` on `f x` (`similar_initial`). The shifted run of
`m'` (`reaches_append_right`) transfers to it (`reaches_of_similar`, using the
shared `similar_step`), ending after `t₂ ≤ p'(|f x|)` more steps in state
`|m| + |m'|`, which is past the concatenated table, with `g (f x)` followed by
blanks (`blankPad_word`). Since `|f x| ≤ q(|x|)` for a polynomial `q`
(`computes_output_poly`), the total `t₁ + t₂ ≤ p(n) + p'(q(n))` is bounded by
one polynomial (`compose_bound`). Correctness composes as for `IsReduction`.
The identity is computed by the empty table in zero steps (`computes_id`).

**Transfer and hardness.** `poly_decider_transfer` is the shared
`inP_of_reduces` (the same table concatenation with a decider as the second
table). `hardness_transfer` is its contrapositive. The hypothesis `¬ InP L` is
met by the shared diagonal language `Diag` (`diag_not_inP`), so
`diag_hardness_transfer` is not vacuous. `firstBit` (first bit `1`) is decided
by a one-row table in one step, is nontrivial, and so receives an unrestricted
reduction from `Diag` (`reduces_to_any_nontrivial`) but no machine reduction
(`reduction_cost_essential`).

**The schema with constants.** In the abstract schema, let `R` satisfy
`R.time x, szB (R.run x) ≤ e(n+1)^k` with `n = szA x`, and let the decider
`D` for `M` satisfy `D.time y ≤ c(szB y + 1)^d`. Since `(n+1)^k ≥ 1`,
`szB (R.run x) + 1 ≤ (e+1)(n+1)^k`, so
`D.time (R.run x) ≤ c((e+1)(n+1)^k)^d = c(e+1)^d (n+1)^(kd)`
(`poly_bound_compose`). Adding `R.time x` and bounding both powers by
`(n+1)^(kd+k)` gives total time `≤ (e + c(e+1)^d)(n+1)^(kd+k)`
(`poly_sum_bound`). Because `time` is declared rather than derived,
`polyDeciderFor_every` shows that the schema's decider predicate holds for
every language; only the machine instance says anything about P.

**Why this is insufficient alone.** Every theorem above moves a decider or
a non-existence statement from one problem to another. P = NP becomes "SAT
has a polynomial decider", and P ≠ NP becomes "SAT has none", but no
reduction theorem decides either. A correct reduction from SAT to a problem
`M` in P would itself be a proof of P = NP, so every such claim must come
with a complete proof of both directions and of the cost bounds; a reduction
in the other direction (`M` to SAT) proves nothing about `M`.

## 5. Known results and literature

* S. A. Cook, "The complexity of theorem-proving procedures", STOC 1971;
  L. A. Levin, "Universal sequential search problems", Problemy Peredachi
  Informatsii 9(3), 1973. SAT is NP-complete under polynomial reductions.
* R. M. Karp, "Reducibility among combinatorial problems", in *Complexity
  of Computer Computations*, Plenum, 1972. Twenty-one NP-complete problems
  via many-one reductions.
* M. R. Garey and D. S. Johnson, *Computers and Intractability*, Freeman,
  1979. Standard catalogue and the reduction methodology used here.
* R. E. Ladner, "On the structure of polynomial time reducibility", JACM
  22(1), 1975. If P ≠ NP there are problems in NP that are neither in P nor
  NP-complete, so "not in P" does not imply "NP-hard".
* L. Berman and J. Hartmanis, "On isomorphisms and density of NP and other
  complete sets", SIAM J. Comput. 6(2), 1977; S. R. Mahaney, "Sparse
  complete sets for NP: solution of a conjecture of Berman and Hartmanis",
  JCSS 25(2), 1982. A sparse NP-complete set would imply P = NP: structural
  facts about reductions can yield collapses, but only from strong
  hypotheses.

## 6. How far the idea can be pushed toward P vs NP

* **Proved (general, machine model):** machine reductions compose
  (`polyReduces_trans`), transfer membership in P backwards
  (`poly_decider_transfer`) and non-membership forwards (`hardness_transfer`,
  `sat_hardness_transfer`), and spread NP-hardness (`npHard_of_reduces`,
  hypothesis `SATHard`).
* **Refuted (general):** one-directional or constant maps as reductions,
  and cost-free reductions as evidence of hardness.
* **Exact remaining obligation:** a proof of P = NP by this route needs a
  machine reduction from `SAT` to some `M` together with `InP M`, that is
  `∃ M, PolyReduces SAT M ∧ InP M`. `sat_reduction_route_iff` proves this is
  equivalent to `InP SAT` (take `M = SAT` and `polyReduces_refl` for the
  converse), so the reduction contributes no progress unless `M` is already
  known to be in P. It yields `PEqualsNP` only under the named hypothesis
  `SATHard` (`pEqualsNP_of_sat_reduction_route`), which is the hardness half
  of Cook–Levin and is not mechanised here. Idea 29 labels this proposition
  as its open obligation (`SATReducesToP`). Symmetrically, a proof of P ≠ NP
  needs `¬ InP` for some NP language, which reductions can then spread
  (`hardness_transfer`) but not create.
* **What a follow-up must check** for any claimed reduction: both
  directions of `IsReduction`, a polynomial bound on running time, and a
  polynomial bound on output size in the *bit* encoding of the target.

## 7. Failure modes this idea catches

* **Invalid reduction** (family 4 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): only one
  direction verified (`yes_preserving_not_sufficient`), or a map that
  collapses instances (`const_not_reduction`).
* **Encoding size** (family 17): a `PolyReduces` machine writes its output
  within its time bound, so its output length is polynomial
  (`computes_output_poly`); a map with exponential blow-up (for example,
  expanding a formula into its truth table) is not a `PolyReduces`.
* **Wrong direction** (family 5): reducing a problem *to* SAT, or reducing
  an easy special case, proves nothing about its hardness; without cost
  bounds every language reduces to every nontrivial one
  (`reduces_to_any_nontrivial`).
* **Hidden exponential work** (family 2): a reduction that decides the
  source instance internally is correct but not polynomial.
* **Circularity** (family 12): assuming the target is in P when the target
  is itself NP-hard.

Audit rule: every claimed reduction must be stated as `PolyReduces`, with
both directions of correctness and the machine and its polynomial step bound
given.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea12.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea12.v
```

Both commands print nothing on success. Remove the generated
`Idea12.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
