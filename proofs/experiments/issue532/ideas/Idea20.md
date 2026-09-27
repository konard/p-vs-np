# Idea 20 — Parallel and physical cost models

**Verdict:** Refuted as a route (general theorem)

Parallel hardware can make time smaller than work, but only by the number of
processors. The files prove, for every schedule, that covering `W` distinct
tasks with at most `p` tasks per round takes `W ≤ p * rounds`, and that a
dependency chain of length `d` takes at least `d` rounds. From this they
derive that `2^n` units of work cannot finish in polynomially many rounds on
polynomially many processors, for all large `n`. They also derive the
abstract form of NC ⊆ P. Physical models escape the bound only if they fail
the resource accounting `work ≤ time * resource`. That this accounting holds
for every realizable device is a postulate of physics, recorded as the
obligation `PhysicalResourceHonesty`, and it is not a mathematical theorem.

## 1. The idea at full strength

Issue #532 Part I item 6 ("Circuits, physics, and speed of light") says:
"Time complexity abstracts *causal dependency*, not wire delay" and
"Different physical models (parallelism, analog, reversibility) may change
invariants". Phase 5 asks to "Change assumptions deliberately" including
"Alternative cost models". Phase 6 lists "NC vs P" as a training ground. At
full strength:

> A sufficiently parallel machine, or a physical process such as analog
> dynamics, optics, DNA or quantum superposition, explores all `2^n`
> assignments simultaneously and so decides SAT in polynomial time. Hence
> "P = NP in the physical world".

## 2. Precise mathematical formulation

* A schedule is `s : List (List Nat)`, a list of rounds of task identifiers.
  * `UsesAtMost p s`: every round has at most `p` tasks.
  * `Covers W s`: every task `t < W` occurs in some round.
  * `totalWork s` is the total number of task executions, which equals the
    length of `flat s`, the sequential execution order.
* A chain of length `d` placed in rounds `round : Nat → Nat` is respected
  when `round i < round (i+1)` for `i + 1 < d`.
* Polynomials have the repository form `polyEval c k n = c * (n+1)^k`.
* A physical run has three functions of input size: `work`, `time` and
  `resource`. It is resource honest when `work n ≤ time n * resource n` for
  all `n`.
* The open obligation is
  `PhysicalResourceHonesty Realizable := ∀ m, Realizable m → ResourceHonest m`.
  `Realizable` is a predicate supplied by physics.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `length_flat`, `mem_flat` | Sequential order of a schedule: length is total work, membership is membership in some round. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `work_bound` | `UsesAtMost p s → totalWork s ≤ p * rounds`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `covers_work` | Covering `W` distinct tasks needs total work at least `W`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `rounds_lower_bound` | `UsesAtMost p s ∧ Covers W s → W ≤ p * rounds`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `span_bound` | A chain of length `d` in strictly increasing rounds below `R` forces `d ≤ R`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `brent_lower_bound` | Both bounds for one schedule: `W ≤ p * rounds` and `d ≤ rounds`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `sequential_simulation` | One processor simulates the schedule in at most `p * rounds` steps. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `poly_parallel_in_poly_sequential` | Polynomial processors and polynomial rounds give work at most `polyEval (c c') (k+k') n` (abstract NC ⊆ P). | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `exp_beats_poly` | `c (n+1)^k < 2^n` for all `n ≥ 2^(2(c+k)+1)`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `exp_work_forces_superpoly_processors` | Covering `2^n` tasks needs `p * rounds ≥ 2^n`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `poly_parallel_cannot_hide_exponential_work` | For all `c k c' k'` and all `n ≥ 2^(2(cc'+k+k')+1)`, a schedule with `≤ c(n+1)^k` processors covering `2^n` tasks has more than `c'(n+1)^k'` rounds. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `schedule_is_honest` | Schedules satisfy the resource accounting, with processors as the resource. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `PhysicalResourceHonesty` (def) | Open (physical) obligation: every realizable run is resource honest. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `physical_conditional` | Under the obligation, a realizable run with work `2^n` and polynomial time uses more than any given polynomial amount of resource, for all large `n`. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |
| `dishonest_model_collapses` | A run with work `2^n`, time 1 and resource 1 is a consistent object and is not resource honest. So the obligation is a genuine postulate. | [Idea20.lean](../lean/Idea20.lean) | [Idea20.v](../rocq/Idea20.v) |

## 4. Complete argument

**Work.** By induction on the schedule, each round contributes its length,
which is at most `p`, so `totalWork s ≤ p * |s|`. If `s` covers
`0, …, W-1`, then `range W ⊆ flat s`. Because `range W` has no duplicates,
`W = |range W| ≤ |flat s| = totalWork s`. Together these give
`W ≤ p * |s|`.

**Span.** If `round i < round (i+1)`, then by induction `i ≤ round i`. For
`d > 0` this gives `d - 1 ≤ round (d-1) < R`, so `d ≤ R`.

**Polynomial resources.** Suppose `p ≤ c(n+1)^k` and `|s| ≤ c'(n+1)^k'`.
Then `totalWork s ≤ p * |s| ≤ cc' (n+1)^(k+k')`. If `s` covers `2^n`
tasks, then `2^n ≤ cc'(n+1)^(k+k')`. For `n ≥ 2^(2(cc'+k+k')+1)` this
contradicts `exp_beats_poly`. The threshold is explicit. The same inequality
read left to right says that a polynomial parallel computation can be
simulated in polynomial sequential time, which is the content of NC ⊆ P
once a machine model is fixed.

*Worked example.* With `n = 20`, `2^20 = 1 048 576` tasks on `p = 1000`
processors need at least `1049` rounds. With `p = n^2 = 400` they need at
least `2622` rounds, far more than `n^2`.

**Physical models.** Abstract away the schedule and keep only three
numbers: elementary operations, time steps, and resource units (processors,
energy, volume, precision bits). If `work ≤ time * resource`, the computation
above applies verbatim (`physical_conditional`). A run that violates this
accounting, doing `2^n` operations in one step with one unit of resource, is
a perfectly consistent mathematical object (`dishonest_model_collapses`).
Whether such runs exist is a question about physics, not mathematics.

## 5. Known results and literature

* R. P. Brent, "The parallel evaluation of general arithmetic expressions",
  *Journal of the ACM* 21(2) (1974). This is the source of the work–span
  scheduling principle: time is at most `W/p + d`, and at least
  `max(W/p, d)`.
* NC ⊆ P, and more generally the simulation of a uniform polynomial-size,
  polynomial-depth parallel computation in polynomial sequential time. These
  are standard facts of parallel complexity theory.
* S. Aaronson, "NP-complete problems and physical reality", *ACM SIGACT
  News* 36(1) (2005). A survey of proposals for solving NP-complete problems
  physically (soap bubbles, analog, relativistic, quantum, etc.) and of where
  each pays an exponential resource.
* C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and
  weaknesses of quantum computing", *SIAM Journal on Computing* 26(5)
  (1997). Black-box search over `N` items needs `Ω(√N)` quantum queries, so
  quantum black-box search over `2^n` assignments needs `Ω(2^(n/2))` queries.
  This does not rule out a quantum algorithm that uses the structure of SAT.
* L. K. Grover, "A fast quantum mechanical algorithm for database search",
  *STOC* 1996. Shows the `O(√N)` upper bound, which is optimal by BBBV.

What is **not** formalized:

* A PRAM, circuit or Turing machine model, and the classes NC and P.
* Quantum query complexity: the BBBV lower bound is only cited.
* Any physical law. `PhysicalResourceHonesty` is a definition, and no
  instance of `Realizable` is given.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** Parallelism changes time by at most the processor
  count. With polynomial processors, a problem in polynomial parallel time
  is in P (`poly_parallel_in_poly_sequential`). So parallel models cannot
  separate or collapse P and NP beyond what sequential models do. At the
  same time, any sequential lower bound transfers to parallel time divided
  by processors.
* **Brute force refuted.** Any algorithm whose work is `2^n`, such as
  exhaustive enumeration, needs superpolynomial `processors × time`
  (`poly_parallel_cannot_hide_exponential_work`).
* **Remaining obligation.** `PhysicalResourceHonesty` for the real world.
  This is an extended Church–Turing style postulate about physics, not a
  statement of complexity theory, and it is neither equivalent to nor
  implied by P ≠ NP. Quantum mechanics fits the framework only through the
  quantum query lower bound, which is cited and covers black-box search
  only. Quantum computers do not obviously satisfy
  `work ≤ time * resource` with classical work, and BQP versus NP is open.
* **Barriers.** None of the standard barriers applies, because the result
  is a bound on brute force, not on SAT. A cleverer sequential algorithm
  would also be a cleverer parallel algorithm, so parallelism reduces the
  question back to P vs NP itself.

## 7. Failure modes this idea catches

* **Family 9 (physical process or nondeterminism).** "The machine explores
  all branches at once" is a nondeterministic or physical model. The
  auditor should ask which resource is being paid exponentially.
  `dishonest_model_collapses` shows exactly what is being assumed.
* **Family 2 (hiding exponential work).** Exponentially many processors,
  exponential precision in analog values, or exponential energy are hidden
  exponential work. `exp_work_forces_superpoly_processors` makes the
  accounting explicit.
* **Family 17 (parameter mistakes).** Counting "time" while ignoring the
  processor count or the precision parameter.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea20.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea20.v
rm -f proofs/experiments/issue532/rocq/Idea20.vo proofs/experiments/issue532/rocq/Idea20.vok \
      proofs/experiments/issue532/rocq/Idea20.vos proofs/experiments/issue532/rocq/Idea20.glob \
      proofs/experiments/issue532/rocq/.Idea20.aux
```

Both commands print nothing on success.
