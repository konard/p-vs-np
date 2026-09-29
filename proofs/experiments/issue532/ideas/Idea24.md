# Idea 24 — Unit propagation

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Unit propagation is sound. The files prove, for every CNF, that a unit
clause forces its literal, that propagating it preserves satisfiability,
and that a derived empty clause certifies unsatisfiability. As a general
decision procedure it is refuted by a formal family: for every pair of
variables and every padding of long clauses, `sq x y ++ ψ` is
unsatisfiable, yet propagation leaves it unchanged. On Horn formulas,
positive unit propagation followed by the all-false assignment decides
satisfiability, and this is proved in full.

## 1. The idea at full strength

Issue #532 Part I item 2 ("Heuristics, optimization, and guarantees") says
that failure of local methods "is a statement about **current algorithmic
paradigms**, not about all possible ones" and asks to "Search for new
invariants". Phase 4 lists "local optimization arguments" among the proof
templates to encode, and says to "record exact failure points". Phase 6
names "restricted SAT variants" as a training ground. Unit propagation is
the simplest local inference rule in every modern SAT solver. At full
strength:

> Repeatedly assign the literal of every unit clause and simplify. Each
> step is forced, cheap and local. If this process always either finds a
> conflict or reaches a formula that is trivially satisfiable, SAT is in
> polynomial time.

## 2. Precise mathematical formulation

* The SAT core is the one used in Ideas 21–23: literals `⟨var, pos⟩`,
  clauses and CNFs as lists, `evalCNF`, `Satisfiable`, `restrict v b φ`
  (drop the clauses containing the literal `⟨v,b⟩`, delete variable `v`
  from the rest), `setVar`, `eval_restrict`, and `size`.
* Propagating a literal `l` means `restrict l.var l.pos φ`.
* `findUnit φ` returns the literal of the first clause of length 1, if any.
* `up n φ` is unit propagation with fuel `n`. With fuel `n+1`, if
  `findUnit φ = some l` it continues with `up n (restrict l.var l.pos φ)`.
  Otherwise it stops.
* `sq x y = {x∨y, x∨¬y, ¬x∨y, ¬x∨¬y}`.
* `posCount C` is the number of positive literals in `C`.
  `IsHorn φ := ∀ C ∈ φ, posCount C ≤ 1`.
* `hornUP n φ` works as follows with fuel `n+1`:
  * it returns `false` if `φ` has an empty clause;
  * it returns `true` if there is no positive unit clause;
  * otherwise it propagates the first positive unit `v` (restricting `v`
    to true) and recurses.

  With fuel 0 it evaluates `φ` under the all-false assignment.
  `hornSolve φ := hornUP (size φ) φ`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `unit_forces` | If `[l] ∈ φ` and `a` satisfies `φ`, then `a` satisfies `l`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `propagate_preserves` | If `a` satisfies `l`, then `φ` and its propagation by `l` have the same value under `a`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `unit_step_equisat` | For a unit clause `[l] ∈ φ`, the propagation is satisfiable iff `φ` is. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `findUnit_some`, `findUnit_none_of_long` | `findUnit` returns a genuine unit clause, and returns nothing when all clauses have length at least 2. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `up_equisat` | For every fuel `n`: `Satisfiable (up n φ) ↔ Satisfiable φ`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `up_conflict_unsat` | An empty clause in `up n φ` proves `φ` unsatisfiable. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `up_noop` | If every clause has length at least 2, then `up n φ = φ`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `sq_unsat` | `sq x y` is unsatisfiable for all `x, y`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `up_incomplete_family` | For every `ψ` with clauses of length at least 2 and all `x y n`: `up n (sq x y ++ ψ)` is `sq x y ++ ψ` itself, contains no empty clause, and the formula is unsatisfiable. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `restrict_horn` | Restriction preserves `IsHorn`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `horn_fixpoint_sat` | A Horn CNF with no empty clause and no positive unit clause is satisfied by the all-false assignment. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `size_restrict_lt` | Propagating a unit clause strictly decreases `size`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `hornUP_correct` | For Horn `φ` with `size φ ≤ n`: `hornUP n φ = true ↔ Satisfiable φ`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |
| `hornSolve_correct` | For every Horn `φ`: `hornSolve φ = true ↔ Satisfiable φ`. | [Idea24.lean](../lean/Idea24.lean) | [Idea24.v](../rocq/Idea24.v) |

There is no open obligation in this idea. Every statement is proved.

## 4. Complete argument

**Soundness.** If `[l] ∈ φ` and `a` satisfies `φ`, the clause `[l]` is
true under `a`, so `a` satisfies `l`, that is `a l.var = l.pos`. By
`eval_restrict`, `φ` restricted by `l` evaluates under `a` exactly as `φ`
evaluates under `setVar a l.var l.pos`. That assignment equals `a`, because
`a` already gives `l.var` the value `l.pos`. Hence propagation preserves
every satisfying assignment that satisfies `l`. Conversely, a model `b` of
the propagated formula yields the model `setVar b l.var l.pos` of `φ`. So
one step is an equisatisfiability, and induction on the fuel extends this
to `up n`. An empty clause is unsatisfiable, so a conflict certifies UNSAT.

**Incompleteness.** `up` acts only through `findUnit`, which fails on
formulas whose clauses all have length at least 2. On such a formula `up`
is the identity for every fuel. The four clauses of `sq x y` cover all four
values of `(a x, a y)`, so `sq x y` is unsatisfiable, and adding clauses
keeps it unsatisfiable. All its clauses have length 2 (when `x = y` a
clause such as `x∨x` still has two literal occurrences). So for every
padding `ψ` of long clauses the formula `sq x y ++ ψ` is a fixpoint of
propagation, contains no empty clause, and is unsatisfiable. The family is
infinite and parametric in `x`, `y` and `ψ`. It is not a single
counterexample.

*Worked example.* `(x₁∨x₂) ∧ (x₁∨¬x₂) ∧ (¬x₁∨x₂) ∧ (¬x₁∨¬x₂)` has no
unit clause, so unit propagation stops immediately with "unknown". One
branching step on `x₁` settles the question. Setting `x₁ = true` leaves
`x₂ ∧ ¬x₂`, and propagation then derives the empty clause; setting
`x₁ = false` gives the same by symmetry. Local inference fails and search
is needed.

**Horn formulas.** Restriction only deletes literals and clauses, so it
never increases the number of positive literals in a clause, and the Horn
property is preserved. Suppose a Horn formula has no empty clause and no
positive unit clause. Every clause then either contains a negative literal
(true under all-false), or is all positive. An all-positive clause has
length equal to its positive count, which is at most 1. It is nonempty, so
it would be a positive unit, which is excluded. So all-false is a model
(`horn_fixpoint_sat`). If there is a positive unit `[v]`, then propagating
it preserves satisfiability (`unit_step_equisat`) and the Horn property,
and it strictly decreases `size` (`size_restrict_lt`). Therefore
`size φ` rounds of fuel suffice, and `hornSolve` is correct on every Horn
formula. Negative unit clauses never need to be propagated: all-false
already satisfies them.

## 5. Known results and literature

* M. Davis and H. Putnam, "A computing procedure for quantification
  theory", *Journal of the ACM* 7(3) (1960), and M. Davis, G. Logemann and
  D. Loveland, "A machine program for theorem-proving", *Communications of
  the ACM* 5(7) (1962). These introduced the one-literal (unit) rule as part
  of DPLL.
* W. F. Dowling and J. H. Gallier, "Linear-time algorithms for testing the
  satisfiability of propositional Horn formulae", *Journal of Logic
  Programming* 1(3) (1984). Horn-SAT is decidable in linear time by unit
  propagation.
* N. D. Jones and W. T. Laaser, "Complete problems for deterministic
  polynomial time", *Theoretical Computer Science* 3(1) (1976). Unit
  resolution (equivalently Horn satisfiability) is P-complete.
* T. J. Schaefer, "The complexity of satisfiability problems", *STOC* 1978.
  In the dichotomy theorem for Boolean constraint languages, Horn and
  dual-Horn are two of the tractable cases, alongside 2-CNF and affine.
* B. Aspvall, M. F. Plass and R. E. Tarjan, "A linear-time algorithm for
  testing the truth of certain quantified Boolean formulas", *Information
  Processing Letters* 8(3) (1979). This gives linear-time 2-SAT. The family
  `sq x y` is 2-CNF, so it is easy for 2-SAT algorithms but invisible to
  unit propagation.

What is **not** formalized:

* Running time. `hornSolve` performs at most `size φ` propagation rounds,
  each a linear scan, which gives a quadratic bound. The linear-time
  Dowling–Gallier data structure and any cost model are not formalized.
* P-completeness of unit resolution.
* Harder families such as pigeonhole or odd-cycle formulas. These are
  optional in the specification and are not needed, because the `sq`
  family already refutes completeness.
* A proof that `up (size φ) φ` reaches a fixpoint. `size_restrict_lt`
  gives the key decrease, but the fixpoint statement for general `up` is
  not stated.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** Unit propagation is a sound polynomial-time
  simplifier and a complete decision procedure for Horn formulas. It is a
  component of every DPLL and CDCL solver, where it is combined with
  branching (Idea 21) and clause learning (resolution, Idea 23).
* **Refuted as a general procedure.** `up_incomplete_family` shows that
  propagation alone cannot decide SAT. Even the 2-CNF fragment escapes it.
* **Limits of the whole family.** Adding branching turns propagation into
  DPLL. DPLL traces are tree-like resolution refutations, and CDCL is
  bounded by general resolution. Both therefore inherit the exponential
  resolution lower bounds cited in Idea 23 (Haken 1985 and successors).
  So no strengthening built from unit propagation, branching and learning
  gives polynomial SAT.
* **Positive frontier.** Horn is an instance of Phase 6's "restricted SAT
  variants". Schaefer's theorem says which restricted Boolean constraint
  languages are tractable and that all others are NP-complete. Unit
  propagation settles the Horn and dual-Horn cases, but not 2-CNF or
  affine formulas.
* **Barriers.** The result is about one algorithm class, so no complexity
  barrier is relevant. It does not bear on P vs NP beyond this class.

## 7. Failure modes this idea catches

* **Family 6 (local instead of global consistency).** Propagation
  checks that no clause is locally violated after forced assignments. On
  `sq x y` every clause is locally consistent, yet no global model exists.
  `up_incomplete_family` is the exact failure point.
* **Family 5 (solving an easier problem).** A procedure that works on Horn
  formulas, or on all tested instances, may solve only a tractable special
  case. `hornSolve_correct` holds only under `IsHorn`.
* **Family 20 (structure theorem from one class).** Showing that
  propagation-based solvers fail says nothing about arbitrary algorithms.
* **Family 8 (heuristics as proof).** Good performance of propagation on
  industrial instances is no guarantee on worst-case families.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea24.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea24.v
rm -f proofs/experiments/issue532/rocq/Idea24.vo proofs/experiments/issue532/rocq/Idea24.vok \
      proofs/experiments/issue532/rocq/Idea24.vos proofs/experiments/issue532/rocq/Idea24.glob \
      proofs/experiments/issue532/rocq/.Idea24.aux
```

Both commands print nothing on success.
