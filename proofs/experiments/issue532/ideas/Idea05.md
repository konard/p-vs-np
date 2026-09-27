# Idea 05 — Greedy optimization

**Verdict:** Refuted as a route (general theorem)

A greedy rule commits to the option that looks cheapest *now*. For every `r`
there is a two-stage instance where that option costs more than `r` times the
optimum. This is machine-checked (`greedy_ratio_unbounded`), so no bound on
greedy's error holds over all instances. The positive side is also
machine-checked: greedy is exact when every option forces the same
continuation cost, and when the decisions are independent (one element per
group, a partition matroid). These are exactly the situations with no
interaction between choices, and NP-hard problems are not like that.

## 1. The idea at full strength

Ambitious version (direction P = NP): hard combinatorial problems (SAT, TSP,
set cover, …) are solved by making a sequence of locally best choices, each
computable in polynomial time. If one greedy rule were exact for an NP-complete
optimization problem, P = NP would follow. A weaker hope is that greedy is
always within a constant factor of optimal.

Source in issue #532: Part I item 2 ("Local optimization can't guarantee
global optimality … This is a statement about **current algorithmic
paradigms**, not about all possible ones … Search for new invariants") and
Part II Phase 4 ("Encode proof templates … local optimization arguments …
Attempt formal proofs → record exact failure points"). The failure point
recorded here is the trap family: an early cheap choice forces an expensive
continuation.

## 2. Precise mathematical formulation

* **Generic selection.** `argminBy f o os` returns an element of `o :: os`
  with the smallest key `f` (the earliest one on ties). The list is given as
  head plus tail, so it is never empty.
* **Two-stage instance.** A nonempty list of options `(first, rest) : ℕ × ℕ`.
  `first` is the cost visible at decision time, and `rest` is the cost the
  choice forces afterwards. `total (a, b) = a + b`.
* **Greedy.** `greedyChoice o os = argminBy fst o os`, and
  `greedyCost o os = total (greedyChoice o os)`.
* **Optimum.** `optCost o os = total (argminBy total o os)`.
* **Trap family.** `(1, k) :: [(2, 0)]`. As a graph: from `s`, an edge of
  cost 1 to `a` then a forced edge of cost `k` to `t`, or an edge of cost 2 to
  `b` then a forced edge of cost 0 to `t`.
* **Independent decisions.** `Picks gs xs` means `xs` picks one element from
  each nonempty group of `gs` (the bases of a partition matroid with capacity
  1 per group). `greedyPicks gs` takes each group's minimum, and `sumList` is
  the total cost.
* **The claim the route needs.** For some NP-hard optimization problem, a
  polynomial-time greedy rule with `greedyCost = optCost` on every instance
  (or at least `greedyCost ≤ c · optCost` for a fixed `c`).

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `argminBy_mem` | `argminBy f o os ∈ o :: os`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `argminBy_le` | For every `p ∈ o :: os`, `f (argminBy f o os) ≤ f p`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `optCost_le` | For every option `p ∈ o :: os`, `optCost o os ≤ total p`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `optCost_achieved` | Some option `p ∈ o :: os` has `total p = optCost o os`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `greedyChoice_mem` | Greedy picks one of the options. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `optCost_le_greedyCost` | `optCost o os ≤ greedyCost o os`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `greedy_optimal_of_uniform_continuation` | If every option has second component `c`, then `greedyCost o os = optCost o os`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `trap_greedyCost` | `greedyCost (1, k) [(2, 0)] = k + 1` for every `k`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `trap_optCost` | `1 ≤ k → optCost (1, k) [(2, 0)] = 2`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `greedy_ratio_unbounded` | For every `r` there are `o, os` with `0 < optCost o os` and `r · optCost o os < greedyCost o os`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `greedyPicks_valid` | `Picks gs (greedyPicks gs)` for every list of nonempty groups. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |
| `greedyPicks_optimal` | `Picks gs xs → sumList (greedyPicks gs) ≤ sumList xs`. | [Idea05.lean](../lean/Idea05.lean) | [Idea05.v](../rocq/Idea05.v) |

Not machine-checked: the general Rado–Edmonds matroid theorem, and the
literature results of Section 5.

## 4. Complete argument

**Selection.** Induction on the tail. For `o :: []` the result is `o`. For
`o :: p :: ps`, let `q = argminBy f p ps`. By induction `q ∈ p :: ps` and
`f q ≤ f x` for every `x ∈ p :: ps`. If `f q < f o` the result is `q`, which is
at most `f o` and at most everything in the tail. Otherwise the result is `o`,
with `f o ≤ f q ≤ f x`.

**Optimum.** `optCost` is `argminBy total`, so the two facts above say exactly
that it is attained and is a lower bound. Greedy returns an option, so its total
is at least the optimum.

**Uniform continuation.** Suppose every option has `rest = c`. Let `p` attain
the optimum. Greedy's first cost is at most `p.1`, so its total is at most
`p.1 + c = total p = optCost`. The reverse inequality always holds.

**Trap family.** Options `(1, k)` and `(2, 0)`. Greedy compares visible costs:
`2 < 1` is false, so it keeps `(1, k)` and pays `1 + k`. The optimum compares
totals `1 + k` and `2`. For `k ≥ 1` the minimum is `2` (for `k = 1` both
options cost 2). Given `r`, take `k = 2r + 1`: the optimum is `2 > 0` and
greedy pays `2r + 2 > 2r = r · 2`.

Worked example: `r = 10`, `k = 21`. Greedy takes the cost-1 edge, is then
forced along a cost-21 edge, and pays 22. The optimum pays 2, and 22 > 10 · 2.

**Independent decisions.** Induction on `Picks`. For a group `(h, t)` with
chosen element `x ∈ h :: t`, the greedy element `m` satisfies `m ≤ x`
(`argminBy_le`), and by induction the greedy sum over the other groups is at
most the chosen sum. Add the two inequalities.

**What the two sides show together.** Greedy is exact exactly when a local
choice does not change what later choices cost. In the trap family it does.
Choosing `(1, k)` forces the continuation `k`, and greedy cannot see this. SAT
has this feature as well: setting one variable decides which clauses the later
variables still have to satisfy. The formal theorem refutes the claim "the
visibly cheapest option is always optimal, or always within a fixed factor".
It does not show that *every* conceivable greedy-style rule fails on every
NP-hard problem. That stronger statement depends on P ≠ NP (Section 6).

## 5. Known results and literature

* R. Rado, "Note on independence functions", *Proc. London Math. Soc.* (3) 7,
  1957. Greedy is optimal for all weights on the independent sets of a matroid.
  (Not formalized; only the partition-matroid special case is proved here.)
* J. Edmonds, "Matroids and the greedy algorithm", *Mathematical Programming*
  1, 1971. The converse: if greedy is optimal for all weight functions on an
  independence system, the system is a matroid. (Not formalized.)
* J. B. Kruskal, "On the shortest spanning subtree of a graph and the
  traveling salesman problem", *Proc. Amer. Math. Soc.* 7, 1956. Greedy is
  exact for minimum spanning trees (a graphic matroid). (Not formalized.)
* D. J. Rosenkrantz, R. E. Stearns, P. M. Lewis II, "An analysis of several
  heuristics for the traveling salesman problem", *SIAM J. Computing* 6(3),
  1977. The nearest-neighbour greedy tour can be a factor `Θ(log n)` worse
  than optimal, even for metric TSP. (Not formalized.)
* S. Sahni and T. Gonzalez, "P-complete approximation problems", *J. ACM*
  23(3), 1976. For general (non-metric) TSP, no polynomial-time algorithm
  achieves any constant approximation ratio unless P = NP. (Not formalized.)

## 6. How far the idea can be pushed toward P vs NP

**At full potential.** By Rado–Edmonds, greedy is exact for *every* weight
function exactly on matroids. Minimum spanning tree, and choosing one element
per group as proved here, are examples. All of these problems are in P. Some
problems are polynomial but not matroids, such as bipartite matching (the
intersection of two matroids). Solving those needs augmenting paths rather than
greedy. So greedy's reach, even at full potential, is a subclass of P.

**Remaining obligation.** None as stated. The route "greedy is exact for an
NP-complete optimization problem" is refuted in its universal form by
`greedy_ratio_unbounded`, and in its approximate form for general TSP by
Sahni–Gonzalez (conditional on P ≠ NP). A new, more powerful "greedy"
would have to choose each step using information about the whole future (the
`rest` component). Computing that information *is* the optimization problem.
The obligation then collapses to Idea 01's `PolySATDecider` (a polynomial SAT
decider, equivalent to P = NP), so no separate `def` is introduced here.

**Barriers.** Inapproximability results (Sahni–Gonzalez, and later
PCP-based bounds) mean that for many NP-hard problems even approximate greedy
exactness would imply P = NP. The Rado–Edmonds characterization is an
unconditional barrier: a rule that is optimal for all weights forces matroid
structure.

## 7. Failure modes this idea catches

* **Local-to-global inference**
  ([error family 6](../../../attempts/COMMON_ERRORS.md#6-replacing-global-consistency-with-local-or-greedy-consistency)):
  "each step is optimal, so the result is optimal" is false in general
  (`trap_greedyCost`, `trap_optCost`).
* **Special-case success**
  ([family 5](../../../attempts/COMMON_ERRORS.md#5-solving-an-easier-special-approximate-or-different-problem)):
  greedy's exactness for independent choices (`greedyPicks_optimal`) or
  uniform continuations does not transfer to problems whose choices interact.
* **Heuristic evidence**
  ([family 8](../../../attempts/COMMON_ERRORS.md#8-treating-heuristics-experiments-or-probability-as-proof)):
  greedy performing well on benchmarks is not a worst-case guarantee.
  `greedy_ratio_unbounded` shows no ratio bound holds for all instances.
* **One algorithm class treated as all algorithms**
  ([family 20](../../../attempts/COMMON_ERRORS.md#20-assuming-a-structure-theorem-for-all-algorithms-from-one-algorithm-class)):
  greedy failing is a statement about greedy, not a lower bound for every
  algorithm. It cannot be used to argue P ≠ NP.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea05.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea05.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea05.{vo,vok,vos,glob}` and
`.Idea05.aux` files.
