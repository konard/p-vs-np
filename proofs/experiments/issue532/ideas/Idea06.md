# Idea 06 — Local search and potential functions

**Verdict:** Refuted as a route (general theorem)

Local search improves a potential (cost) by moving to neighbouring states. It
is exact only when every local minimum is global. For SAT with cost "number of
falsified clauses", no fixed flip radius `k` is exact: for every `k` there is a
satisfiable formula with a positive-cost local minimum (`bounded_flip_not_exact`).
Every CNF *does* have an exact neighbourhood of size one
(`exists_size_one_exact_neighbourhood`), and with any exact neighbourhood local
search decides SAT after at most `m + 1` rounds (`exact_local_search_decides`).
So the entire difficulty is *computing* an exact neighbourhood. All theorems
named here are machine-checked. The further statement that computing an exact
neighbourhood efficiently is as hard as solving SAT is an informal argument
(Section 6), not a formal theorem.

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
* **Exactness.** `ExactAll cost nbr :⇔` every local minimum is a global
  minimum over all of `α`.
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
* **The claim the route needs.** A neighbourhood `N φ` for every CNF that is
  exact for `unsatCount · φ` and that can be *searched* in time polynomial in
  `|φ|`.

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
| `bounded_flip_not_exact` | For every `k`: `trapCNF k` is satisfiable, `unsatCount (all-false) (trapCNF k) = 1`, and every `b` with `Within k (k+1) all-false b` has `unsatCount (all-false) (trapCNF k) ≤ unsatCount b (trapCNF k)` (all-false is a local minimum of the radius-`k` flip neighbourhood). | [Idea06.lean](../lean/Idea06.lean) | [Idea06.v](../rocq/Idea06.v) |

Not machine-checked: the PLS results and the other literature in Section 5.

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
obligation is a neighbourhood that is exact and whose improving neighbour (or
certificate that none exists) can be computed in time polynomial in `|φ|`.
With `exact_local_search_decides` this gives a polynomial SAT decider. Conversely,
if P = NP, then a minimum-`unsatCount` assignment can be computed in
polynomial time (binary search on the optimum plus self-reduction), which
gives an exact, efficiently searchable neighbourhood. So, by this informal
argument together with the cited Cook–Levin theorem (neither is formalized
here), the obligation is equivalent to Idea 01's `PolySATDecider`, i.e. to
P = NP.
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
