# Idea 06 — Local search and potential functions

**Verdict:** Refuted as a route (general theorem)

Local search improves a potential (cost) by moving to neighbouring states. It
is exact only when every local minimum is global. For SAT with cost "number of
falsified clauses", no fixed flip radius `k` is exact: for every `k` there is a
satisfiable formula with a positive-cost local minimum (`bounded_flip_not_exact`).
Every CNF *does* have an exact neighbourhood of size one
(`exists_size_one_exact_neighbourhood`), and with any exact neighbourhood local
search decides SAT after at most `m + 1` rounds (`exact_local_search_decides`).
So the entire difficulty is *computing* a local minimum of an exact
neighbourhood. In the shared machine model this is the open obligation
`ExactLocalSearch`: a polynomial-time `Complexity.Machine` attaches to every
instance a local minimum of an exact neighbourhood. Given the named known
theorem `CNFEvalInP` (CNF evaluation is in P, not mechanised here), it puts SAT
in P (`inP_sat_of_exactLocalSearch`), and with `SATHard` it gives P = NP
(`pEqualsNP_of_exactLocalSearch`). The neighbourhood part is free
(`exactLocalSearch_of_globalMin`), so the obligation amounts to computing a
minimum-cost assignment in polynomial time. It is not vacuous: not every
language is solved by exact local search (`not_forall_localSearchSolves`). The
converse (SAT ∈ P gives the obligation, by self-reduction) is argued in
Section 6 and is not mechanised.

## 1. The idea at full strength

Ambitious version (direction P = NP): find a potential function and a
neighbourhood structure such that (i) neighbourhoods are polynomial-size and
polynomial-time searchable, (ii) every local optimum is a global optimum, and
(iii) improving walks are short. Local search would then solve an NP-complete
problem in polynomial time. A weaker hope is that a clever potential escapes
the traps of the obvious one.

Source in issue #532: Part I item 2 ("Local optimization can't guarantee
global optimality … It assumes locality, fixed neighborhoods, and classical
cost landscapes … ✖ We don't know whether a different global invariant exists
… Search for new invariants") and Part II Phase 4 ("local optimization
arguments … Attempt formal proofs → record exact failure points"). The recorded
failure points are `line_never_reaches_global` (landscapes),
`bounded_flip_not_exact` (SAT with fixed-radius moves), and
`exists_size_one_exact_neighbourhood` (exactness without efficiency is free).

## 2. Precise mathematical formulation

* **Landscape.** A state type `α`, a cost `cost : α → ℕ`, and a neighbourhood
  `nbr : α → List α`.
* **Local minimum.** `IsLocalMin cost nbr s :⇔ ∀ t ∈ nbr s, cost s ≤ cost t`.
* **Exactness (schema).** `ExactAllFor cost nbr :⇔` every local minimum is a
  global minimum over all of `α`. Here `cost` is the potential being
  minimised, not a running time.
* **Improving walk.** `ImpPath cost nbr s u`: a chain of neighbour moves that
  strictly decrease cost.
* **Line landscape.** States `0..n`, `lineNbr n i = {i−1, i+1} ∩ [0, n]`,
  `trapCost M n i = 0` if `i = n`, else `M + i`.
* **Local search.** `localSearch cost nbr fuel s` repeatedly moves to the first
  improving neighbour, at most `fuel` times. `searchEvals` counts neighbour
  evaluations (list lengths scanned).
* **SAT landscape.** States are assignments `ℕ → Bool`, and the cost is
  `unsatCount a φ`, the number of clauses falsified.
* **Flip radius.** `Within k n a b :⇔ ∃ S, |S| ≤ k ∧ ∀ i < n, a i ≠ b i → i ∈ S`
  (`b` differs from `a` on at most `k` of the variables `0..n−1`).
* **Trap formula.** `trapCNF k = (x_0 ∨ … ∨ x_k) ∧ ⋀_{i,j ≤ k} (¬x_i ∨ x_j)`.
* **Machine model** (`Machines`; time is the `Run` step count of a
  `Complexity.Machine`). The CNFs of the shared layer are translated by
  `ofM`, and `sat_ofM : SAT w = true ↔ Satisfiable (ofM (decode w))`. An
  assignment prefix is written self-delimitingly by `pack` (each bit `b`
  becomes `1 b`, then `0`), split off again by `splitPacked`, and read as
  `assignOf bits i = bits.getD i false`.
* **CNF evaluation.** `EvalLang w` evaluates the CNF `decode` of the rest of
  `w` under the packed assignment at the front of `w`. The named known theorem
  is `CNFEvalInP : Prop := InP EvalLang`.
* **The claim the route needs**, as a machine statement:

```lean
def LocalSearchSolves (L : Language) : Prop :=
  ∃ (N : CNF → Assignment → List Assignment) (m : Machine) (f g : Word → Word)
    (p : Polynomial),
    (∀ φ, ExactAllFor (fun a => unsatCount a φ) (N φ)) ∧ Machines.Computes m g p ∧
    ∀ x, L x = Machines.SAT (f x) ∧ ∃ bits, g x = pack bits ++ f x ∧
      IsLocalMin (fun a => unsatCount a (ofM (Machines.decode (f x))))
        (N (ofM (Machines.decode (f x)))) (assignOf bits)

/-- Open obligation. -/
def ExactLocalSearch : Prop := LocalSearchSolves Machines.SAT
```

  A machine `m` maps each input `x` within `p` steps to a SAT instance `f x`
  (with the same answer), with a local minimum of an exact neighbourhood for
  that instance written in front.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `line_strict_local_min` | For `n ≥ 2` and every `M`: every neighbour `t` of `0` has `trapCost M n 0 < trapCost M n t`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `line_global_min` | `trapCost M n n ≤ trapCost M n t` for all `t`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `line_local_not_global` | For `M ≥ 1`, `n ≥ 2`: `0` is a local minimum and `trapCost M n n < trapCost M n 0`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `line_basin` | If `i + 2 ≤ n` and an improving walk goes from `i` to `t`, then `t + 2 ≤ n`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `line_never_reaches_global` | If `i + 2 ≤ n`, no improving walk goes from `i` to `n`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `full_neighbourhood_exact` | If `U` contains every state, the neighbourhood `fun _ => U` is exact. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `singleton_exact_neighbourhood` | If `best` is a global minimum, `fun _ => [best]` is exact. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `descending_length_le` | A strictly cost-decreasing list `s :: rest` has `|rest| ≤ cost s`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `localSearch_localMin` | If `cost s < fuel`, `localSearch cost nbr fuel s` is a local minimum. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `localSearch_evals_le` | If all neighbourhoods have size `≤ B`, then `searchEvals cost nbr f s ≤ f · B`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `unsatCount_eq_zero_iff` | `unsatCount a φ = 0 ↔ evalCNF a φ = true`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `exact_local_search_decides` | If `nbr` is exact for `unsatCount · φ`, then for every start `a`, the result of `localSearch` with fuel `unsatCount a φ + 1` satisfies `φ` iff `Satisfiable φ`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `bestAssign_min` | `unsatCount (bestAssign φ) φ ≤ unsatCount t φ` for every assignment `t` (`bestAssign` is exhaustive search over `2^(numVars φ)` vectors). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `exists_size_one_exact_neighbourhood` | There is `N : CNF → Assignment → List Assignment` with `|N φ a| = 1` and `N φ` exact for `unsatCount · φ`, for every `φ`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `trapCNF_allTrue` | All-true satisfies `trapCNF k`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `trapCNF_allFalse_cost` | `unsatCount (all-false) (trapCNF k) = 1`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `trapCNF_near_allFalse` | If `Within k (k+1) all-false b`, then `evalCNF b (trapCNF k) = false`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `sat_ofM`, `splitPacked_pack`, `evalLang_pack` | Translation to the shared CNF syntax; the packed prefix splits off; `EvalLang (pack bits ++ x)` evaluates `decode x` under `assignOf bits`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `CNFEvalInP` | Named known theorem (not mechanised): `InP EvalLang`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `ExactLocalSearch` | Open obligation: `LocalSearchSolves Machines.SAT`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `localMin_decides` | With an exact neighbourhood, a local minimum satisfies `φ` iff `φ` is satisfiable. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `localSearchSolves_reduces` | `LocalSearchSolves L` gives a polynomial-time machine reduction `L x = EvalLang (g x)`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `inP_of_localSearchSolves` | `CNFEvalInP → LocalSearchSolves L → InP L`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `inP_sat_of_exactLocalSearch` | `CNFEvalInP → ExactLocalSearch → InP SAT`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `pEqualsNP_of_exactLocalSearch` | `SATHard → CNFEvalInP → ExactLocalSearch → PEqualsNP`. | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `exactLocalSearch_of_globalMin` | A polynomial-time machine attaching a globally minimal assignment to every input already gives `ExactLocalSearch` (the neighbourhood is free). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `exists_not_reducible` | For every language `M`, some language has no polynomial-time machine reduction to `M` (Cantor over machines). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `not_forall_localSearchSolves` | Non-vacuity: not every language is solved by exact local search (unconditional). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |
| `bounded_flip_not_exact` | For every `k`: `trapCNF k` is satisfiable, `unsatCount (all-false) (trapCNF k) = 1`, and every `b` with `Within k (k+1) all-false b` has `unsatCount (all-false) (trapCNF k) ≤ unsatCount b (trapCNF k)` (all-false is a local minimum of the radius-`k` flip neighbourhood). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |

Not machine-checked: the PLS results and the other literature in Section 5,
the known theorem `CNFEvalInP`, and the converse of the conditional theorem
(Section 6). The schema `ExactAllFor` was called `ExactAll` before the move to
the machine model; the Rocq file still uses the old name.

## 4. Complete argument

**Line landscape.** The only neighbour of `0` is `1` (as `n ≥ 2`). Its cost is
`M + 1`, since `1 ≠ n`, and the cost of `0` is `M`. So `0` is a strict local
minimum, while state `n` has cost `0 < M`. **Basin.** From `s ≤ n − 2` the
neighbours are `s − 1` (cost `M + s − 1`, improving) and `s + 1 ≤ n − 1` (cost
`M + s + 1`, not improving). So every improving move stays in `0..n−2`, and by
induction on the walk the global minimum is never reached. Worked example:
`M = 100`, `n = 1000`. Starting anywhere in `0..998`, greedy descent ends at
`0` with cost 100, while the optimum is 0 at state 1000.

**SAT trap for every radius `k`.** In `trapCNF k`, the clause
`x_0 ∨ … ∨ x_k` excludes all-false, and `¬x_i ∨ x_j` excludes every assignment
with some `x_i = true` and some `x_j = false` (`i, j ≤ k`). So on `x_0..x_k` only
all-true satisfies the formula. All-false violates only the first clause (cost
1). Now let `b` flip at most `k` of the `k + 1` variables away from all-false.
By pigeonhole (`range (k+1) ⊄ S` when `|S| ≤ k`), some `x_i` stays false. If
some `x_j` is true, clause `¬x_j ∨ x_i` fails. Otherwise all of `x_0..x_k` are
false and the first clause fails. Either way the cost is `≥ 1`. So all-false is a
local minimum of the radius-`k` neighbourhood with cost 1, and the global
minimum 0 is at Hamming distance `k + 1`. Worked example, `k = 2`: 3 variables,
`1 + 9 = 10` clauses. All-false costs 1, and every assignment with one or two
ones costs `≥ 1`, while `(1,1,1)` costs 0. The radius-`k` neighbourhood has
`Σ_{d≤k} C(n,d)` elements, which is polynomial for fixed `k`, and it is never
exact. To be exact on this family the radius has to grow with the number of
variables.

**Exactness is free if efficiency is ignored.** `bestAssign φ` minimises
`unsatCount` over the `2^(numVars φ)` vectors of the relevant variables. By
congruence (only variables `< numVars φ` matter), it is a global minimum over
all assignments. The neighbourhood "jump to `bestAssign φ`" has size one and is
exact. It is not efficiently computable, because computing it is exhaustive
search (Idea 01).

**Exact neighbourhoods decide SAT quickly.** Every improving move lowers
`unsatCount` by at least 1, so from start `a` there are at most `unsatCount a φ ≤ m`
moves, where `m` is the number of clauses (`descending_length_le`). With fuel
`unsatCount a φ + 1`, local search ends at a local minimum
(`localSearch_localMin`). With an exact neighbourhood, that local minimum is
global, so it has cost 0 iff `φ` is satisfiable. The number of neighbour
evaluations is at most `(m + 1) · B` (`localSearch_evals_le`). Combined with
`exists_size_one_exact_neighbourhood`, this shows that *counting neighbour
evaluations* cannot separate good neighbourhoods from bad ones: the cost is
hidden in generating the neighbourhood list.

**The machine version.** Suppose `LocalSearchSolves L`, with the machine `m`
computing `g` within `p` steps. For every input `x`, `g x = pack bits ++ f x`,
where `assignOf bits` is a local minimum of an exact neighbourhood for
`φ = ofM (decode (f x))`. By exactness it is a global minimum, so it satisfies
`φ` iff `φ` is satisfiable (`localMin_decides`). Since `splitPacked` recovers
`bits` and `f x`, `EvalLang (g x)` is exactly that evaluation
(`evalLang_pack`), and by `sat_ofM` it equals `SAT (f x) = L x`. So `m` is a
polynomial-time reduction of `L` to `EvalLang` (`localSearchSolves_reduces`),
and `Machines.inP_of_reduces` together with `CNFEvalInP` puts `L` in P. The
neighbourhood can always be taken to be the size-one exact one, so it is enough
for a machine to attach a globally minimal assignment
(`exactLocalSearch_of_globalMin`). For non-vacuity, Cantor's argument over
machines (`Machines.exists_language_not_in_family`) gives a language that no
machine reduces to `EvalLang`. That language is not solved by exact local
search, and this needs no known theorem (`not_forall_localSearchSolves`).

## 5. Known results and literature

* D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, "How easy is local
  search?", *J. Computer and System Sciences* 37(1), 1988. Defines the class
  PLS of local search problems. (Not formalized.)
* A. A. Schäffer and M. Yannakakis, "Simple local search problems that are
  hard to solve", *SIAM J. Computing* 20(1), 1991. Local Max-Cut under the
  flip neighbourhood is PLS-complete, and the standard local search algorithm
  can need exponentially many improving steps. (Not formalized. In our SAT
  landscape walks are short, because costs are bounded by `m`.
  With weights, as in weighted Max-Cut, they need not be.)
* C. H. Papadimitriou and K. Steiglitz, *Combinatorial Optimization:
  Algorithms and Complexity*, Prentice-Hall, 1982. Introduces exact
  neighbourhoods and discusses why NP-hard problems such as TSP are not
  expected to have exact neighbourhoods that can be searched in polynomial time.
  (Not formalized.)
* U. Schöning, "A probabilistic algorithm for k-SAT and constraint
  satisfaction problems", FOCS 1999. Randomized local search solves 3-SAT in
  expected time `O*((4/3)^n)`, which is exponential and the best-known type of
  guarantee for local search on SAT. (Not formalized.)
* B. Selman, H. Levesque, D. Mitchell, "A new method for solving hard
  satisfiability problems", AAAI 1992 (GSAT). An empirically strong local
  search with no worst-case guarantee. (Not formalized.)
* V. Klee and G. J. Minty, "How good is the simplex algorithm?", in
  *Inequalities III*, 1972. A local-improvement method with an exact
  neighbourhood (simplex pivots are exact for linear programming) can still
  take exponentially many steps. (Not formalized.)

## 6. How far the idea can be pushed toward P vs NP

**At full potential.** For problems with polynomially bounded integer costs
(like `unsatCount`), improving walks are automatically short, so local search
is a polynomial-time exact algorithm whenever the neighbourhood is exact and
searchable in polynomial time. `exact_local_search_decides` and `localSearch_evals_le` are
the conditional theorem.

**Remaining obligation.** The spec's naive obligation, "a polynomial-size exact
neighbourhood", is *provably satisfied* (`exists_size_one_exact_neighbourhood`),
so it is not an obligation at all, and no `def` for it is introduced. The real
obligation is stated in the shared machine model:

```lean
def ExactLocalSearch : Prop := LocalSearchSolves Machines.SAT
```

A polynomial-time `Complexity.Machine` must output, for every instance, a local
minimum of an exact neighbourhood (for SAT itself, or for a SAT instance it
produces). Running local search with an exact, efficiently searchable
neighbourhood for `unsatCount φ + 1 ≤ m + 1` rounds (`exact_local_search_decides`,
`localSearch_evals_le`) is one way to build such a machine. Composing machine
rounds is not mechanised, so the obligation asks for the result of the search.
Mechanised consequences:

* `inP_sat_of_exactLocalSearch : CNFEvalInP → ExactLocalSearch → InP Machines.SAT`;
* `pEqualsNP_of_exactLocalSearch : Machines.SATHard → CNFEvalInP → ExactLocalSearch → PEqualsNP`;
* `not_forall_localSearchSolves` (non-vacuity);
* `exactLocalSearch_of_globalMin`: the exact neighbourhood itself costs
  nothing, and all the content is in computing a minimum.

The hypotheses are known theorems that are not mechanised here. `CNFEvalInP`
says that evaluating a CNF under a given assignment is in P (Cook 1971;
Arora–Barak Ch. 2). `SATHard` is the hardness half of Cook–Levin. Conversely,
if P = NP, a minimum-`unsatCount` assignment can be computed in polynomial
time. The question "is there an assignment falsifying at most `k` clauses?" is
in NP, hence in P. Binary search on `k` finds the optimum, and self-reduction
(fixing one variable at a time) finds an assignment attaining it. `exactLocalSearch_of_globalMin`
then gives `ExactLocalSearch`. This converse is argued informally and is not
mechanised. So `ExactLocalSearch` is equivalent to P = NP, and the route is
Idea 01's `PolySATDecider` in another guise.
`bounded_flip_not_exact` rules out every fixed-radius flip neighbourhood,
the most natural efficiently searchable family.

**Barriers.** PLS-completeness (Johnson–Papadimitriou–Yannakakis;
Schäffer–Yannakakis) shows that even *finding a local optimum* can be hard
for natural weighted neighbourhoods. The Klee–Minty phenomenon shows that
exactness alone does not bound the number of steps when costs are
unbounded. For SAT the trap family defeats every fixed radius.

## 7. Failure modes this idea catches

* **Local-to-global inference**
  ([error family 6](../../../attempts/COMMON_ERRORS.md#6-replacing-global-consistency-with-local-or-greedy-consistency)):
  a claimed "no improving move ⇒ optimal" step must come with an exactness
  proof. `line_local_not_global` and `bounded_flip_not_exact` refute it for
  line landscapes and all fixed flip radii.
* **Hidden exponential work**
  ([family 2](../../../attempts/COMMON_ERRORS.md#2-hiding-exponential-work-in-a-claimed-polynomial-algorithm)):
  a neighbourhood that "contains the optimum" (like `bestAssign`) or a radius
  that grows with `n` hides exhaustive search. Counting only neighbour
  evaluations (`searchEvals`) misses this cost.
* **Heuristic evidence**
  ([family 8](../../../attempts/COMMON_ERRORS.md#8-treating-heuristics-experiments-or-probability-as-proof)):
  GSAT/WalkSAT success on benchmarks is not a worst-case guarantee.
* **One algorithm class treated as all algorithms**
  ([family 20](../../../attempts/COMMON_ERRORS.md#20-assuming-a-structure-theorem-for-all-algorithms-from-one-algorithm-class)):
  the failure of flip-neighbourhood search is not a lower bound for all
  algorithms and cannot support P ≠ NP.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea06.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea06.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea06.{vo,vok,vos,glob}` and
`.Idea06.aux` files.
