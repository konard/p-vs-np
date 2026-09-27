# Idea 40 — Size-uniform invariant (induction with resource bounds)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Induction on the input size proves that a recursive algorithm is correct.
Whether it is fast depends on how cost grows from size `n` to `n + 1`. The files
prove, in general, that additive growth (`T(n+1) ≤ T(n) + q(n)` with `q`
polynomial) gives a polynomial bound, and that multiplicative growth
(`T(n+1) ≥ 2 T(n)`, i.e. two recursive calls) gives at least `2^n`, which beats
every polynomial. A self-reduction for SAT with one recursive call of the same
answer and polynomial step cost would be a polynomial-time SAT algorithm. That
obligation is stated in the shared machine model (`Issue532.Machines`, time =
`Complexity.Run` step count) as `SATMachineSelfReduction`: a polynomial-time
machine step that removes one variable and keeps satisfiability, plus a machine
for variable-free formulas. The Lean file proves that it gives `InP SAT`, and
with `SATHard` gives `PEqualsNP`. Two known theorems enter only as named
hypotheses: `IterationClosure` (iterating a length-non-increasing
polynomial-time map `|x|` times stays polynomial) and `SATHard` (Cook–Levin).
The abstract-cost version survives as the schema `AdditiveSelfReductionFor`.

## 1. The idea at full strength

A frequent pattern in claimed polynomial SAT algorithms:

1. define an invariant `P(n)`: "the algorithm is correct on all formulas with
   `n` variables";
2. prove `P(0)` and `P(n) → P(n+1)` by eliminating one variable;
3. conclude correctness for all `n`, and claim that the running time is
   polynomial "because each step is polynomial".

Steps 1–2 are sound (`tested` is a restatement of natural-number induction). Step 3 is the
problem: it is valid only if the step from `n+1` to `n` makes **one** recursive
call. The obvious elimination, trying `x = 0` and `x = 1`, makes two calls. At
full strength, the idea asks for a size-reducing step that keeps the answer and
makes one call. That is exactly an additive-cost self-reduction.

## 2. Precise mathematical formulation

- The additive recurrence is `T 0 ≤ c` and `∀ n, T (n+1) ≤ T n + q n`, with `q`
  monotone. The polynomial case is `q n = a · (n+1)^k`.
- The multiplicative recurrences are `T 0 = 1`, `T (n+1) = 2 · T n` (doubling)
  and `T 0 ≥ 1`, `T (n+1) ≥ 2 · T n` (branching). `branchCost q` is
  `1` at `0` and `2 · branchCost q n + q n` at `n+1`.
- A polynomial bound is `c · (n+1)^k`, as in the repository's
  `proofs/complexity` library.
- A self-reduction solver `run base step n I` applies `step` `n` times, then
  answers with `base`. `runCost baseCost stepCost step n I` is the base cost
  plus the step cost at each level.
- **Schema.** `AdditiveSelfReductionFor size answer` requires `base`, `step`,
  `baseCost`, `stepCost`, and `c a k` such that `base` is correct on size-0
  instances, `baseCost ≤ c`, `step` maps size `n+1` to size `n` and preserves
  `answer`, and `stepCost I ≤ a · (size I + 1)^k`. The costs are free
  functions, so this is only the cost-accounting skeleton; `poly_solver_for`
  and `self_reduction_solver_bound` are its theorems.
- **Machine model.** Words are `Complexity.Word`, SAT is the shared language
  `Issue532.Machines.SAT`, and the size of a word is
  `satSize x = numVars (decode x)`, the number of variables of the formula it
  denotes (`satSize_le_length`: `satSize x ≤ |x|`). `iter f n x` applies `f`
  `n` times. `MachineSelfReductionOf L` is:

  ```lean
  def MachineSelfReductionOf (L : Language) : Prop :=
    ∃ (m : Machine) (f : Word → Word) (p : Polynomial) (d : Machine) (q : Polynomial),
      Computes m f p ∧ (∀ x, (f x).length ≤ x.length) ∧
      (∀ x, satSize (f x) ≤ satSize x - 1 ∧ L (f x) = L x) ∧
      DecidesOn d q (fun y => satSize y = 0) L
  ```

  The step map is computed by a `Complexity.Machine` within the polynomial `p`
  (`Computes`), never lengthens the word, removes one variable and keeps the
  answer; the base machine `d` decides `L` within `q` on variable-free formulas.
- **Open obligation.** `def SATMachineSelfReduction : Prop := MachineSelfReductionOf SAT`.
- **Known theorem (hypothesis, not mechanised).**

  ```lean
  def IterationClosure : Prop :=
    ∀ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p →
      (∀ x, (f x).length ≤ x.length) →
      ∃ (m' : Machine) (p' : Polynomial), Computes m' (fun x => iter f x.length x) p'
  ```

  Running a polynomial-time, length-non-increasing map `|x|` times with a
  counter costs at most `|x| · (p(|x|) + O(|x|))` on a multi-tape machine, and
  one tape simulates it with quadratic overhead (Sipser, 3rd ed., Theorem 7.8;
  Arora–Barak, Claim 1.6). The Cook–Levin hardness of SAT is the shared
  hypothesis `SATHard`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | small illustration kept from an earlier round (not a main result): the natural-number induction principle, restated | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `additive_bound` | `T 0 ≤ c`, `T(n+1) ≤ T n + q n`, `q` monotone give `T n ≤ c + n · q n` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `additive_poly_closed` | `c + n · a(n+1)^k ≤ (c+a)(n+1)^(k+1)` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `additive_poly` | additive polynomial steps give `T n ≤ (c+a)(n+1)^(k+1)` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `doubling_exact` | `T 0 = 1`, `T(n+1) = 2 T n` give `T n = 2^n` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `branching_lower` | `T 0 ≥ 1`, `T(n+1) ≥ 2 T n` give `T n ≥ 2^n` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `exp_beats_poly` | `c(n+1)^k < 2^n` for all `n ≥ 2^(2(c+k)+1)` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `poly_lt_two_pow` | for all `c, k` there is `n` with `c(n+1)^k < 2^n` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `branching_not_poly` | a branching recurrence has no bound `c(n+1)^k` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `doubling_not_poly` | for all `c, k` the doubling recurrence exceeds `c(n+1)^k` somewhere | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `branchCost_exponential` | two recursive calls cost at least `2^n`, whatever the overhead | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `run_correct` | a same-answer size-reducing step plus a correct base give a correct solver | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `runCost_bound` | with `baseCost ≤ c` and polynomial step cost, `runCost ≤ c + n · a(n+1)^k` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `AdditiveSelfReductionFor` | schema (abstract costs): a one-call self-reduction with base cost `≤ c` and step cost `≤ a(size+1)^k` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `poly_solver_for` | schema theorem: `AdditiveSelfReductionFor` gives a correct solver of cost `≤ c'(size+1)^k'` (existential over `solve` and `cost`; the next row is the explicit form) | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `self_reduction_solver_bound` | for any `base`, `step`, `baseCost`, `stepCost` meeting the obligation's conditions, `run base step (size I) I = answer I` and `runCost … ≤ (c+a)(size I + 1)^(k+1)` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `satSize_le_length` | a word of length `n` denotes a formula with at most `n` variables (via `numVars_decodeAux_le`, `clauseBound_append`) | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `MachineSelfReductionOf` | machine one-call self-reduction for a language: polynomial-time `Computes` step, length non-increasing, one variable fewer, same answer, `DecidesOn` base machine | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `SATMachineSelfReduction` | **open obligation**: `MachineSelfReductionOf SAT` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `IterationClosure` | known theorem, hypothesis only: `Computes m f p` and `f` length non-increasing give a machine computing `x ↦ iter f (length x) x` in polynomial time | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `iterate_spec` | `n` steps lower the size by `n` and keep the answer | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `iterate_length_spec` | `length x` steps reach size `0` with the answer of `x` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `inP_of_machineSelfReduction` | `IterationClosure → MachineSelfReductionOf L → InP L` (composition by `inP_of_promise_reduction`) | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `inP_sat_of_machineSelfReduction` | `IterationClosure → SATMachineSelfReduction → InP SAT` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `pEqualsNP_of_machineSelfReduction` | `IterationClosure → SATHard → SATMachineSelfReduction → PEqualsNP` | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |
| `not_forall_machineSelfReductionOf` | non-vacuity: not every language has a machine self-reduction (Cantor over pairs of machines, via `encPair_injective` and `machineSelfReductionOf_eq`) | [Lean](../lean/Idea40.lean) | [Rocq](../rocq/Idea40.v) |

Helper lemmas `succ_le_two_pow`, `lt_two_pow_self`, `linear_lt_exp` and
`dyadic_bracket` are proved in both files. The definitions `branchCost`, `run`,
`runCost` and the schema appear in both files. The recurrence and schema proofs
are constructive; the non-vacuity part uses classical choice (`mapOf`,
`acceptsOf`). Both files check `branchCost (fun _ => 0) 5 = 32` by computation.

## 4. Complete argument

**Additive case.** By induction on `n`:

    T(n+1) ≤ T(n) + q(n) ≤ c + n·q(n) + q(n) ≤ c + n·q(n+1) + q(n+1) = c + (n+1)·q(n+1),

using monotonicity of `q` (`additive_bound`). For `q(n) = a(n+1)^k`:

    c + n·a(n+1)^k ≤ c(n+1)^(k+1) + a(n+1)^(k+1) = (c+a)(n+1)^(k+1)

(`additive_poly_closed`, `additive_poly`). The degree rises by one: `n` steps,
each polynomial.

**Multiplicative case.** `T(n+1) = 2T(n)` with `T(0) = 1` gives `T(n) = 2^n`
(`doubling_exact`). With `≥` in place of `=`, the same induction gives
`T(n) ≥ 2^n` (`branching_lower`). Adding a nonnegative overhead only helps, so
`branchCost q n ≥ 2^n` (`branchCost_exponential`).

**Exponential beats polynomial.** First, `a(q+1) < 2^q` for `q ≥ 2a+1`
(`linear_lt_exp`). For `n ≥ 2^(2(c+k)+1)`, bracket `2^L ≤ n < 2^(L+1)`. Then
`L ≥ 2(c+k)+1`, so `c + k(L+1) < n`, and

    c(n+1)^k ≤ c · 2^((L+1)k) < 2^c · 2^((L+1)k) ≤ 2^n

(`exp_beats_poly`, `poly_lt_two_pow`). With `branching_lower` this gives
`branching_not_poly` and `doubling_not_poly`.

**Self-reduction.** If `step` maps size `n+1` to size `n` and preserves the
answer, induction on `n` shows `run base step n I = answer I` whenever
`size I = n` (`run_correct`). The cost satisfies the additive recurrence
instance-wise: `runCost (n+1) I = stepCost I + runCost n (step I)`, with
`stepCost I ≤ a(n+2)^k`. The additive argument therefore gives
`runCost ≤ c + n·a(n+1)^k` (`runCost_bound`), and `additive_poly_closed` turns this
into `(c+a)(size+1)^(k+1)` (`self_reduction_solver_bound`,
`poly_solver_for`).

**Machine version.** Let `m` compute the step `f` (obligation
`MachineSelfReductionOf L`). By induction, `satSize (iter f n x) ≤ satSize x - n`
and `L (iter f n x) = L x` (`iterate_spec`). Since `satSize x ≤ |x|`
(`satSize_le_length`, by recursion on the parser `decodeAux`), `iter f |x| x` is
variable-free and has the answer of `x` (`iterate_length_spec`). By
`IterationClosure` a machine computes `x ↦ iter f |x| x` in polynomial time; this
is a machine map into the promise `satSize = 0`, on which `d` is correct, so
`inP_of_promise_reduction` gives `InP L` (`inP_of_machineSelfReduction`). For
`L = SAT` this is `inP_sat_of_machineSelfReduction`, and
`pEqualsNP_of_inP_sat` with `SATHard` gives `pEqualsNP_of_machineSelfReduction`.

**Non-vacuity.** If `MachineSelfReductionOf L` holds with machines `m, d`, then
`L x` is the answer of `d` on `iter (mapOf m) |x| x`, where `mapOf m` is the map
`m` computes (unique by `computes_unique`) and the answer is unique by
`run_deterministic` (`machineSelfReductionOf_eq`). So every such `L` lies in a
family indexed by pairs of machines, which have an injective encoding
(`encPair_injective`); `exists_language_not_in_family` gives a language outside
it (`not_forall_machineSelfReductionOf`).

**Where SAT stands.** The standard self-reduction of SAT, `φ ↦ φ[x:=0], φ[x:=1]`,
reduces the number of variables by one and preserves the answer as a
disjunction of **two** calls. Its cost is `branchCost`, at least `2^n`. Picking
the correct branch in polynomial time is exactly what `SATMachineSelfReduction`
demands. That is deciding satisfiability of `φ[x:=0]`, which is the original
problem on one fewer variable.

## 5. Known results and literature

- M. Davis, H. Putnam, "A computing procedure for quantification theory",
  *Journal of the ACM* 7(3), 1960, and M. Davis, G. Logemann, D. Loveland, "A
  machine program for theorem-proving", *Communications of the ACM* 5(7), 1962.
  DPLL is the branching self-reduction with pruning. Its runs correspond to
  tree-like resolution refutations, so resolution lower bounds such as Haken's
  (*Theoretical Computer Science* 39, 1985) give exponential lower bounds for
  DPLL on unsatisfiable formulas. Not formalized (Idea 27 treats resolution).
- SAT is self-reducible, and search reduces to decision. With a polynomial-time
  decision procedure for SAT, `step` can pick a branch preserving
  satisfiability (and then simplify the formula so that it does not grow). So
  `SATMachineSelfReduction` is implied by P = NP. This converse direction is
  standard (S. Arora and B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009, Section 2.5) but is not
  formalized. The forward direction is formalized modulo the named hypotheses
  `IterationClosure` and `SATHard`.
- J. L. Bentley, D. Haken, J. B. Saxe, "A general method for solving
  divide-and-conquer recurrences", *SIGACT News* 12(3), 1980. This is the
  general theory of recurrences `T(n) = a T(n/b) + f(n)`. Size-reducing-by-one
  recurrences, as here, are the simplest case. Not formalized.

## 6. How far the idea can be pushed toward P vs NP

**Fully developed.** The files give the complete accounting for size-induction
algorithms. One call per level with polynomial overhead gives polynomial cost.
Two calls per level give at least `2^n`, whatever the overhead, and nothing in
between is possible for recurrences of these two forms. Any correctness proof
by induction on size therefore turns into a polynomial-time claim only after
proving the additive recurrence.

**The obligation.** `SATMachineSelfReduction`: a `Complexity.Machine` step map
computable in polynomial time (`Computes m f p`), length non-increasing,
removing one variable (`satSize (f x) ≤ satSize x - 1`) and keeping `SAT`, plus
a machine `d` with `DecidesOn d q (fun y => satSize y = 0) SAT`. The file proves
`IterationClosure → SATMachineSelfReduction → InP SAT` and, with `SATHard`,
`PEqualsNP`. `IterationClosure` (iteration of a polynomial-time map) and
`SATHard` (Cook–Levin) are known theorems stated as hypotheses, not proved.
Conversely, P = NP gives such a step by search-to-decision (cited, not
formalized), so the obligation is as hard as P = NP.
`not_forall_machineSelfReductionOf` shows the machine predicate is a real
constraint: it fails for some language.

**Why it is hard.** A same-answer step on SAT must decide, in polynomial time,
which value of a variable preserves satisfiability. That is the decision problem
itself on a smaller instance. Pruning heuristics (unit propagation, pure
literals, clause learning) reduce the branching on many instances, but the
Haken lower bound shows that DPLL-style branching needs exponentially many calls
on the pigeonhole formulas. Removing the branching requires an idea that is not
captured by resolution.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 2 (hiding exponential work):** "each step is polynomial" with two
  recursive calls per step hides a factor `2^n`. `branchCost_exponential` shows
  that no overhead bound rescues it.
- **Family 12 (circular reasoning):** a step that "chooses the satisfiable
  branch" presupposes a SAT decision procedure. The obligation makes this
  explicit.
- **Family 7 (counting or enumeration mistakes):** counting levels (`n`) instead
  of recursion-tree nodes (`2^n`).
- **Family 10 (provability vs complexity):** a correct induction proof of
  correctness says nothing about time. Only `runCost_bound` does.

Audit rule: for a size-induction algorithm, write down the cost recurrence and
count recursive calls per level. One call with polynomial overhead is
polynomial. Two or more calls on size `n - 1` is exponential.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea40.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea40.v
rm -f proofs/experiments/issue532/rocq/Idea40.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea40.aux
```

Both commands print nothing on success.
