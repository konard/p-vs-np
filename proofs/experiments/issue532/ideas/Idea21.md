# Idea 21 — Exact SAT branching (DPLL splitting)

**Verdict:** Refuted in full strength (published theorem) + formal core

Splitting on a variable is a correct and complete way to decide SAT. The
files prove the splitting rule `sat_split` for every CNF. They also prove
that the pure splitting solver and a DPLL-style solver with pruning are
correct for every CNF whose variables lie in the branching list. The
unpruned split tree has exactly `2^|vs|` leaves, and the pruned tree has at
most that many. That no branching heuristic avoids exponential time on some
families is a published theorem. DPLL and CDCL runs correspond to resolution
refutations, and resolution has exponential lower bounds (Haken 1985 and
successors). Those lower bounds are cited, not formalized.

## 1. The idea at full strength

Issue #532 Part I item 7 ("NP-hardness and P vs NP") says that
"NP-hardness tells us **where structure fails**" and that "Repeated failure
patterns can be formalized and eliminated". Phase 4 ("Systematic
elimination of proof strategies") asks to "Attempt formal proofs → record
exact failure points". Part I item 2 adds that "Failure of known heuristics
≠ impossibility of all methods". The research log entry for this idea
records the core fact that "an existential Boolean branch is equivalent to
its two cases". At full strength the idea reads:

> Branch on one variable at a time, simplify, and prune dead branches.
> With a clever enough choice of the branching variable, clause learning,
> and propagation, the search tree stays polynomial on every formula, so
> SAT ∈ P (toward P = NP).

The claim that would be needed is: *some DPLL/CDCL-style procedure runs in
polynomial time on every CNF*.

## 2. Precise mathematical formulation

* Literals are `⟨var, pos⟩`. Clauses are lists of literals and CNFs are
  lists of clauses. An assignment is `Nat → Bool`. `Satisfiable φ` means
  `∃ a, evalCNF a φ = true`.
* `restrict v b φ` fixes variable `v` to value `b`. It drops every clause
  that contains the literal `⟨v, b⟩` (`clauseHas v b C`), and deletes all
  remaining literals on `v` from the other clauses (`removeVar v C`).
* `setVar a v b` is the assignment that agrees with `a` except that `v` is
  mapped to `b`.
* `VarsIn φ vs` means every literal of `φ` has its variable in `vs`.
* `solve vs φ` is pure splitting. At `vs = []` it evaluates `φ` under the
  all-false assignment. At `v :: vs'` it returns
  `solve vs' (restrict v true φ) || solve vs' (restrict v false φ)`.
* `dpll vs φ` is the same procedure with pruning. It returns `true` when
  `φ = []` and `false` when `φ` contains the empty clause, before
  branching.
* `leaves vs φ` and `dpllLeaves vs φ` count the leaves of the two
  recursion trees.
* The claim that would be needed for P = NP along this route is that, for a
  fixed branching procedure, the number of leaves on every CNF of size `m`
  is at most a fixed polynomial in `m`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `evalClause_setVar` | `evalClause (setVar a v b) C = clauseHas v b C ‖ evalClause a (removeVar v C)`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `eval_restrict` | For all `a v b φ`: `evalCNF a (restrict v b φ) = evalCNF (setVar a v b) φ`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `setVar_self` | Resetting `v` to its own value changes nothing. This is an equality of functions in Lean and pointwise in Rocq. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `sat_split` | For every CNF `φ` and variable `v`: `Satisfiable φ ↔ Satisfiable (restrict v true φ) ∨ Satisfiable (restrict v false φ)`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `mem_removeVar`, `mem_restrict` | Literals left by `removeVar v` are old literals not on `v`. Clauses of a restriction are `removeVar v` of old clauses. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `restrict_vars` | `VarsIn φ (v :: vs) → VarsIn (restrict v b φ) vs`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `eval_congr` | Two assignments that agree on the variables of `φ` give the same value. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `sat_no_vars` | A CNF with no variables is satisfiable iff the all-false assignment satisfies it. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `solve_correct` | For all `vs φ` with `VarsIn φ vs`: `solve vs φ = true ↔ Satisfiable φ`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `leaves_eq` | For all `vs φ`: `leaves vs φ = 2 ^ length vs`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `empty_clause_unsat` | A CNF containing the empty clause is unsatisfiable. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `dpll_correct` | For all `vs φ` with `VarsIn φ vs`: `dpll vs φ = true ↔ Satisfiable φ`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |
| `dpllLeaves_le` | For all `vs φ`: `dpllLeaves vs φ ≤ 2 ^ length vs`. | [Idea21.lean](../lean/Idea21.lean) | [Idea21.v](../rocq/Idea21.v) |

Differences between the two files:

* Lean tests `φ = []` and `[] ∈ φ` in `dpll` as decidable propositions.
  Rocq uses the Boolean tests `isNil φ` and
  `existsb isEmptyClause φ`, and relates the second to `In [] φ` by the
  lemma `existsb_isEmpty`.
* Rocq proves `setVar_self` pointwise, because function extensionality is
  not part of its core. `sat_split` is proved in Rocq via `eval_congr`
  instead.

## 4. Complete argument

**Restriction is evaluation.** Fix `a`, `v` and `b`, and go by induction on
a clause `C = l :: C'`.

* If `l.var = v`, then under `setVar a v b` the literal `l` is true exactly
  when `l.pos = b`. That is exactly when `l` witnesses `clauseHas v b C`.
  `removeVar` drops `l`.
* If `l.var ≠ v`, the literal has the same value under `a` and under
  `setVar a v b`, and `removeVar` keeps it.

In both cases the induction hypothesis closes the goal, which gives
`evalClause_setVar`. For a CNF, clauses with `clauseHas v b C = true` are
satisfied under `setVar a v b` and are dropped by `restrict`. The other
clauses evaluate to `evalClause a (removeVar v C)`. This proves
`eval_restrict`.

**Splitting.** Suppose `a` satisfies `φ`. Since `setVar a v (a v)` agrees
with `a` everywhere, `eval_restrict` shows that `a` satisfies
`restrict v (a v) φ`, which is one of the two branches. Conversely, if `a`
satisfies `restrict v b φ`, then `setVar a v b` satisfies `φ`, again by
`eval_restrict`. This gives `sat_split`.

**Correctness of the solvers.** The proof is by induction on `vs`.

* If `vs = []` and `VarsIn φ []`, then `φ` has no literals. Every
  assignment gives it the same value (`eval_congr`), so evaluating under
  all-false decides it (`sat_no_vars`).
* If `vs = v :: vs'`, both restrictions have their variables in `vs'`
  (`restrict_vars`). By the induction hypothesis and `sat_split`, the
  disjunction of the recursive answers is exactly `Satisfiable φ`.
* For `dpll` there are two extra cases. The empty CNF is satisfied by every
  assignment. A CNF with the empty clause is unsatisfiable
  (`empty_clause_unsat`).

**Tree size.** The unpruned tree branches twice at each of the `|vs|`
levels, whatever the formula. So `leaves vs φ = 2^|vs|` exactly,
independent of `φ`. Pruning only cuts subtrees, so
`dpllLeaves vs φ ≤ 2^|vs|`.

*Worked example.* For `n = 30` variables the unpruned tree has
`2^30 = 1 073 741 824` leaves on every input, including the satisfiable
single-clause formula `x₀`. With `x₀` first in the branching list,
pruning handles that formula in 2 leaves.

**Why pruning is not enough.** Upper bounds on tree size are easy. The real
question is a lower bound on the pruned tree for a clever branching order.
Two tempting shortcuts do not work:

* The complete CNF with all `2^n` clauses over `n` variables forces a full
  split tree. But that formula has size `n·2^n`, so the tree is linear in
  the input size. This is the parameter trap of family 17.
* One slow branching order says nothing about the best order.

The correct statement goes through proof complexity. The trace of a DPLL
run on an unsatisfiable formula, with any branching order, is a tree-like
resolution refutation of the same size. Each leaf is labelled by a clause
falsified by its path, and each internal node is a resolution step on the
branching variable. CDCL traces with restarts correspond to general
resolution. So any lower bound on resolution refutation size is a lower
bound on DPLL/CDCL running time, whatever the heuristic.

## 5. Known results and literature

* M. Davis and H. Putnam, "A computing procedure for quantification
  theory", *Journal of the ACM* 7(3) (1960).
* M. Davis, G. Logemann and D. Loveland, "A machine program for
  theorem-proving", *Communications of the ACM* 5(7) (1962). This is the
  DPLL splitting procedure.
* A. Haken, "The intractability of resolution", *Theoretical Computer
  Science* 39 (1985). The pigeonhole formulas `PHP^{n+1}_n` need
  resolution refutations of size exponential in `n`.
* A. Urquhart, "Hard examples for resolution", *Journal of the ACM* 34(1)
  (1987). Tseitin formulas on expander graphs need exponential-size
  resolution refutations.
* V. Chvátal and E. Szemerédi, "Many hard examples for resolution",
  *Journal of the ACM* 35(4) (1988). Random 3-CNFs with suitable
  clause/variable ratio need exponential resolution with high probability.
* P. Beame, H. Kautz and A. Sabharwal, "Towards understanding and
  harnessing the potential of clause learning", *Journal of Artificial
  Intelligence Research* 22 (2004). This relates clause learning to general
  resolution.
* K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT
  solvers as resolution engines", *Artificial Intelligence* 175(2) (2011).
  CDCL with restarts polynomially simulates general resolution.

What is **not** formalized:

* Resolution itself. See Idea 23 for the soundness of resolution and the
  Cook–Reckhow framework.
* The simulation of DPLL runs by tree-like resolution.
* All the lower bounds listed above.
* Any running-time model beyond the leaf count of the recursion tree.

## 6. How far the idea can be pushed toward P vs NP

* **What is proved.** Splitting is sound and complete (`solve_correct`,
  `dpll_correct`), and its trivial worst-case bound is `2^n` leaves
  (`leaves_eq`, `dpllLeaves_le`).
* **Refuted in full strength.** By the published theorems in Section 5, for
  every branching heuristic, DPLL (tree-like resolution) and CDCL (general
  resolution) take time exponential in the input size on the pigeonhole,
  Tseitin and random 3-CNF families. So no member of this algorithm family
  is a polynomial SAT algorithm. That is an unconditional theorem, but only
  about this family.
* **What remains open.** A polynomial SAT algorithm outside the resolution
  family is not excluded. Excluding all algorithms is the P ≠ NP question
  itself. No new obligation is defined here. The algorithmic obligation is
  the exact polynomial decider of Idea 01/22 (`ExactPolyDecider` in Idea
  22), and the proof-complexity obligation (every proof system
  superpolynomial, equivalent to NP ≠ coNP) is `NoPolyBoundedProofSystem`
  in Idea 23.
* **Barriers.** Resolution lower bounds are proved against a restricted
  model, so relativization and natural proofs do not block them. They also
  say nothing about unrestricted algorithms, so they cannot be lifted to
  P ≠ NP without a new idea (family 20).

## 7. Failure modes this idea catches

* **Family 2 (hiding exponential work).** A "polynomial" solver that is
  secretly a splitting tree. `leaves_eq` makes the `2^n` count explicit.
* **Family 8 (heuristics or experiments as proof).** "Our branching
  heuristic solved all benchmarks quickly" is no proof of a polynomial worst
  case. Haken's pigeonhole family defeats every heuristic in the DPLL/CDCL
  family.
* **Family 20 (structure theorem for all algorithms from one class).** Lower
  bounds for DPLL/CDCL do not transfer to all algorithms. Conversely,
  `dpll_correct` shows that a correct solver needs no special structure
  beyond `sat_split`.
* **Family 17 (parameter mistakes).** Measuring the tree against the number
  of variables instead of the input size, as in the complete-CNF example of
  Section 4.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea21.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea21.v
rm -f proofs/experiments/issue532/rocq/Idea21.vo proofs/experiments/issue532/rocq/Idea21.vok \
      proofs/experiments/issue532/rocq/Idea21.vos proofs/experiments/issue532/rocq/Idea21.glob \
      proofs/experiments/issue532/rocq/.Idea21.aux
```

Both commands print nothing on success.
