# Idea 12 — Reduction verification

**Verdict:** Correct tool, insufficient alone (general theorem proved). Many-one reductions are exactly the right instrument for moving algorithms and hardness between problems, and this is proved in general: correctness transfers (`decider_transfer`), polynomial deciders pull back along polynomial reductions and polynomial reductions compose, both with explicit constants (`poly_decider_transfer`, `poly_reduction_comp`), and hardness pushes forward (`hardness_transfer`). These cost statements are proved in an abstract model where an algorithm's running time is a given function not tied to any machine (see Section 2), so they are bookkeeping lemmas about how bounds compose; connecting them to P and NP requires a concrete machine model, which is not done here. The same general theorems show why reductions cannot settle P vs NP by themselves and catch the recurring "invalid reduction" error: constant maps are never reductions from a nontrivial language, and a yes-to-yes check alone accepts such maps (`const_not_reduction`, `yes_preserving_not_sufficient`), and without cost bounds every language reduces to every nontrivial one (`reduces_to_any_nontrivial`).

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

**Cost model.** An algorithm `Algo α β` is a pair `(run, time)` of an
input–output function and a running time on each input. Input sizes are
given by `sz : α → ℕ`.

* `PolyBounded sz t :≡ ∃ c d, ∀ x, t x ≤ c · (sz x + 1)^d`.
* `PolyDecider sz L :≡` some algorithm computes `L` with polynomially
  bounded time.
* `PolyReduction szA szB L M R :≡ IsReduction R.run L M` and there are
  `e, k` with `R.time x ≤ e (szA x + 1)^k` and
  `szB (R.run x) ≤ e (szA x + 1)^k`. The output-size bound is explicit; on a
  real machine it follows from the time bound, but in an abstract model it
  must be stated, and forgetting it is the classic encoding-size mistake.
* Composition of algorithms runs the first, then the second on its output,
  and adds the running times.
* Caveat: `time` is an arbitrary field, not derived from executing `run` on a
  machine. In this abstract model `PolyDecider sz L` therefore holds for
  every `L` (take `run = L` and `time = 0`; not stated as a theorem), so the
  hypothesis `¬ PolyDecider` of `hardness_transfer` can never be met here.
  The theorems are valid for any cost semantics that adds running times
  under composition; the P vs NP reading needs them instantiated with a real
  machine model (for example Idea 01's), which these files do not do.

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
| `poly_bound_compose` | `a ≤ e(n+1)^k` and `b ≤ c(a+1)^d` imply `b ≤ c(e+1)^d (n+1)^(kd)`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_sum_bound` | `e(n+1)^k + C(n+1)^(kd) ≤ (e+C)(n+1)^(kd+k)`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_decider_transfer` | A polynomial reduction to `M` and a polynomial decider for `M` give a polynomial decider for `L`. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `poly_reduction_comp` | The composition of two polynomial reductions is a polynomial reduction. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |
| `hardness_transfer` | If `L` has no polynomial decider and reduces polynomially to `M`, then `M` has none. | [Lean](../lean/Idea12.lean) | [Rocq](../rocq/Idea12.v) |

In Rocq, `reduction_id` and `reduction_comp` state the defining equations
directly (`∀ x, L x = L (id x)` and `∀ x, L x = N (g (f x))`), because the
section fixes distinct type variables; they are the same statements.
No theorem in either file proves or refutes P = NP.

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

**Polynomial transfer with constants.** Let `R` satisfy
`R.time x, szB (R.run x) ≤ e(n+1)^k` with `n = szA x`, and let the decider
`D` for `M` satisfy `D.time y ≤ c(szB y + 1)^d`. Since `(n+1)^k ≥ 1`,
`szB (R.run x) + 1 ≤ (e+1)(n+1)^k`, so
`D.time (R.run x) ≤ c((e+1)(n+1)^k)^d = c(e+1)^d (n+1)^(kd)`
(`poly_bound_compose`). Adding `R.time x` and bounding both powers by
`(n+1)^(kd+k)` gives total time `≤ (e + c(e+1)^d)(n+1)^(kd+k)`
(`poly_sum_bound`), and the composed algorithm computes `M (R.run x) = L x`.
The same two lemmas bound the time and the output size of a composition of
two polynomial reductions. `hardness_transfer` is the contrapositive of
`poly_decider_transfer`.

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

* **Proved (general):** reductions transfer deciders and hardness with
  explicit polynomial constants, and compose.
* **Refuted (general):** one-directional or constant maps as reductions,
  and cost-free reductions as evidence of hardness.
* **Exact remaining obligation:** a proof of P = NP by this route needs a
  single object, a `PolyReduction` from SAT to some `M` together with
  `PolyDecider M`. In a real machine model, `poly_decider_transfer` shows
  this implies a polynomial decider for SAT, and conversely (take `M` = SAT
  and the identity reduction); by the cited Cook–Levin theorem that is
  P = NP itself (the machine-model instantiation and Cook–Levin are not
  formalized here). The reduction contributes no
  progress unless `M` is already known to be in P. Symmetrically, a proof of
  P ≠ NP needs `¬ PolyDecider` for some NP problem, which reductions can
  then spread (`hardness_transfer`) but not create.
* **What a follow-up must check** for any claimed reduction: both
  directions of `IsReduction`, a polynomial bound on running time, and a
  polynomial bound on output size in the *bit* encoding of the target.

## 7. Failure modes this idea catches

* **Invalid reduction** (family 4 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): only one
  direction verified (`yes_preserving_not_sufficient`), or a map that
  collapses instances (`const_not_reduction`).
* **Encoding size** (family 17): `PolyReduction` demands a polynomial
  output-size bound; an exponential blow-up (for example, expanding a
  formula into its truth table) destroys `poly_decider_transfer`.
* **Wrong direction** (family 5): reducing a problem *to* SAT, or reducing
  an easy special case, proves nothing about its hardness; without cost
  bounds every language reduces to every nontrivial one
  (`reduces_to_any_nontrivial`).
* **Hidden exponential work** (family 2): a reduction that decides the
  source instance internally is correct but not polynomial.
* **Circularity** (family 12): assuming the target is in P when the target
  is itself NP-hard.

Audit rule: every claimed reduction must be stated as `PolyReduction` with
both directions, the time bound and the output-size bound proved.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea12.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea12.v
```

Both commands print nothing on success. Remove the generated
`Idea12.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
