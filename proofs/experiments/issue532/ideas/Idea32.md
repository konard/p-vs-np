# Idea 32 — Promise algorithms

**Verdict:** Developed to an open obligation (conditional theorem proved)

A *promise algorithm* for a language `L` on a promise `P` only has to answer correctly on inputs that satisfy `P`. Two general facts are proved, in Lean and Rocq.

* **Negative (flip at `x`).** Take any promise, any language, and any input `x` outside the promise. Some algorithm is correct on the whole promise and wrong at `x` (`flip_at`). So promise-correctness is total correctness *exactly* when the promise covers all inputs (`promise_total_iff`).
* **Conditional positive.** Suppose a map `f` sends every input into the promise and preserves the answer. Then every promise solver, composed with `f`, is a total solver, at additive cost (`promise_reduction_total`, `compose_cost`). The "into the promise" condition is also necessary (`composition_works_iff`).

For CNF, the Unique-SAT promise excludes the satisfiable formula `x0 ∨ x1`. So some algorithm that is correct on the promise calls it unsatisfiable (`usat_solver_wrong`). A different promise makes SAT trivial (`trivial_promise_solver`), which shows that promise problems can be genuinely easier.

The open obligation is a **deterministic** polynomial-time map from all CNFs into the Unique-SAT promise that preserves satisfiability (`IsolationObligation`). Given that map, any Unique-SAT promise solver decides SAT (`isolation_solves_sat`). Only a *randomized* map with a weaker guarantee is known (Valiant–Vazirani 1986): it keeps unsatisfiable formulas unsatisfiable and gives a satisfiable formula a unique solution only with probability `Ω(1/n)`. Nothing here decides P vs NP.

## 1. The idea at full strength

Research-log item 32 says: "Promise algorithms ... correctness on a promise leaves an outside input wrong". The obligation it names is: "Prove the promise covers all reductions from the NP-complete target or give a total solver."

Issue #532, Part II, Phase 6 ("Positive frontier") lists "restricted SAT variants", "average-case complexity" and "promise problems", and says: "These serve as **training grounds**". Part I, item 7 says: "Negative knowledge is progress". Phase 7 asks to "Build a complete, formal map of why every known path fails — and what remains unblocked."

At full strength, the idea is: find a promise on which SAT becomes easy, for example "at most one satisfying assignment". Solve SAT on the promise, then argue that the promise is "without loss of generality". The theorems below show exactly when that last step is valid. It is valid if and only if every input is mapped into the promise, and it must be done by a total, answer-preserving map.

## 2. Precise mathematical formulation

* `CorrectOn P L A :≡ ∀ x, P x → A x = L x`, for `P : α → Prop` and `L A : α → Bool`.
* CNF core: literals `⟨var, pos⟩`, clauses, CNFs, `evalCNF`, `Satisfiable φ :≡ ∃ a, evalCNF a φ = true`, and `vars φ`.
* The Unique-SAT promise:
  `AtMostOneSolution φ :≡ ∀ a b, evalCNF a φ → evalCNF b φ → ∀ v ∈ vars φ, a v = b v`.
  So `φ` is unsatisfiable or has exactly one solution on its variables.
* `twoWay := [[x0, x1]]`, i.e. `x0 ∨ x1`.
* `EmptyPromise φ :≡ Satisfiable φ ∨ hasEmpty φ`, where `hasEmpty` tests for an empty clause.
* SAT itself enters as a parameter `sat : CNF → Bool` with `hsat : ∀ φ, sat φ = true ↔ Satisfiable φ`. No particular SAT algorithm is assumed.
* The obligation, with the time class `PolyTime` kept as a parameter:

```lean
def IsolationObligation (PolyTime : (CNF → CNF) → Prop) : Prop :=
  ∃ f : CNF → CNF, PolyTime f ∧ (∀ φ, AtMostOneSolution (f φ)) ∧
    ∀ φ, Satisfiable φ ↔ Satisfiable (f φ)
```

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `flip_at` | `x ∉ P` ⇒ some `A` is correct on `P` and wrong at `x` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `promise_correct_not_total` | An input outside `P` ⇒ some promise-correct `A` is not total | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `promise_reduction_total` | `f` into `P`, answer-preserving ⇒ `A ∘ f` is total for every promise solver `A` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `composition_works_iff` | Composition works for every promise solver ⇔ `f` maps into `P` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `promise_total_iff` | Promise correctness is total ⇔ `P` covers everything | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `compose_cost` | Cost of `A ∘ f` is `≤ p(n) + r(q(n))` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `twoWay_satisfiable` | `x0 ∨ x1` is satisfiable | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `not_unique_example` | `x0 ∨ x1` violates the Unique-SAT promise | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `unique_example` | `x0` satisfies the Unique-SAT promise | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `usat_solver_wrong` | Some Unique-SAT promise solver answers `false` on the satisfiable `x0 ∨ x1` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `hasEmpty_unsat` | A CNF with an empty clause is unsatisfiable | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `trivial_promise_solver` | On `EmptyPromise`, "no empty clause" decides SAT | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `trivial_solver_wrong` | That solver is wrong on `x0 ∧ ¬x0` (outside the promise) | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `isolation_solves_sat` | `IsolationObligation` + Unique-SAT promise solver ⇒ total SAT solver `A ∘ f` with `f ∈ PolyTime` | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |
| `decider_meets_isolation` | Given a SAT decider, `isolate` maps into the promise and preserves satisfiability | [Idea32.lean](../lean/Idea32.lean) | [Idea32.v](../rocq/Idea32.v) |

Hypotheses are the same in both files. Decidable equality on the input type is a type-class argument in Lean (`[DecidableEq α]`) and an explicit `eq_dec` argument in Rocq. `composition_works_iff` and `promise_total_iff` also assume that the promise is decidable (`[DecidablePred P]` or `Pdec`), so that the forward direction is constructive. Rocq additionally defines `lit_eq_dec` and `cnf_eq_dec`. Lean derives `DecidableEq` for `Lit`.

## 4. Complete argument

**Flip at `x`.** Define `A y := if y = x then ¬L x else L y`. For `y ∈ P` we have `y ≠ x`, since `x ∉ P`, so `A y = L y`. At `x`, `A x = ¬L x ≠ L x`. The construction needs only decidable equality, not decidability of `L` or of `P`.

**Composition.** If `P (f x)` and `L x = M (f x)`, then `A (f x) = M (f x) = L x` for every `A` correct on `P`. For the converse, suppose some `f x` lies outside `P`. Flipping `M` at `f x` gives a promise-correct `A` with `A (f x) ≠ M (f x) = L x`. So the composition fails for that `A`. Taking `f = id` gives `promise_total_iff`. **Cost.** The composed algorithm runs `f` and then `A`. If `f` takes `≤ p(n)` steps, produces outputs of size `≤ q(n)`, and `A` takes `≤ r(m)` steps with `r` monotone, the total is `≤ p(n) + r(q(n))`. That is polynomial when `p, q, r` are.

**Unique-SAT.** The assignments `a ≡ true` and `b = (v ↦ v = 0)` both satisfy `x0 ∨ x1` and differ at `x1 ∈ vars`. So `x0 ∨ x1` is outside the promise, and `flip_at` produces a promise-correct algorithm with `A (x0 ∨ x1) = ¬sat (x0 ∨ x1) = false`. In contrast, every solution of `x0` has `a 0 = true`, so `x0` is inside the promise.

**Promises can trivialize SAT.** On `EmptyPromise`, an input without an empty clause is satisfiable by the promise. An input with an empty clause is unsatisfiable (`hasEmpty_unsat`). So `¬hasEmpty` is correct on the promise, in linear time. Outside the promise it fails, for example on `x0 ∧ ¬x0`. This is the formal content of "promise problems can be easier". Correctness on a promise says nothing about hard inputs that the promise excludes.

**The obligation.** `isolation_solves_sat` combines `promise_reduction_total` with the promise solver. `decider_meets_isolation` shows why the obligation is *only* hard because of its time bound. With a SAT decider in hand, map satisfiable formulas to `[]` (which has one solution modulo no variables) and unsatisfiable ones to `[[]]`. So the obligation cannot be met by exhibiting some satisfiability-preserving map into the promise. The map must be computed in polynomial time *without* deciding SAT. Using a decider to build `f` would be circular.

## 5. Known results and literature

* S. Even, A. L. Selman, Y. Yacobi, "The complexity of promise problems with applications to public-key cryptography", *Information and Control* 61 (1984). This paper introduced promise problems.
* L. G. Valiant, V. V. Vazirani, "NP is as easy as detecting unique solutions", *Theoretical Computer Science* 47 (1986). It gives a randomized polynomial-time reduction from SAT to the Unique-SAT promise problem. Unsatisfiable formulas stay unsatisfiable, and satisfiable ones get a unique solution with probability `Ω(1/n)`. Consequently, a polynomial-time algorithm for promise-Unique-SAT would give NP = RP. It would not directly give P = NP.
* K. Mulmuley, U. V. Vazirani, V. V. Vazirani, "Matching is as easy as matrix inversion", *Combinatorica* 7 (1987). This is the isolation lemma, again randomized.
* O. Goldreich, "On promise problems: a survey", in *Theoretical Computer Science: Essays in Memory of Shimon Even*, LNCS 3895 (2006).

None of these is formalized here. In particular, the Valiant–Vazirani reduction and its probability analysis are not formalized. Only the deterministic, general skeleton (flip, composition, and the two CNF examples) is formalized.

## 6. How far the idea can be pushed toward P vs NP

The open obligation:

```lean
def IsolationObligation (PolyTime : (CNF → CNF) → Prop) : Prop :=
  ∃ f : CNF → CNF, PolyTime f ∧ (∀ φ, AtMostOneSolution (f φ)) ∧
    ∀ φ, Satisfiable φ ↔ Satisfiable (f φ)
```

`isolation_solves_sat` turns it plus a Unique-SAT promise solver into a SAT solver. Proving P = NP along this route therefore needs **two** things, neither of which is known:

1. a *deterministic* polynomial-time isolation map; only a randomized one that succeeds with probability `Ω(1/n)` is known (Valiant–Vazirani), and whether isolation can be derandomized is open;
2. a polynomial-time algorithm for SAT on the Unique-SAT promise. By Valiant–Vazirani such an algorithm would already give NP = RP, and no such algorithm is known.

`composition_works_iff` shows that nothing weaker than "`f` maps *every* input into the promise" can work for arbitrary promise solvers. A reduction that is only "usually" into the promise gives only a heuristic or randomized solver. `decider_meets_isolation` shows that the correctness part of the obligation is trivial. All the difficulty is in the time bound.

Barriers. Valiant–Vazirani relativizes, so the randomized reduction works relative to every oracle. Any argument that derandomizes it *and* solves Unique-SAT would, if relativizing, contradict Baker–Gill–Solovay (1975). On the lower-bound side, proving that promise-Unique-SAT has no polynomial-time algorithm would in particular prove P ≠ NP (if P = NP, the SAT decider itself is a promise solver), so it is at least as hard as P ≠ NP.

Relation to other ideas: restricted SAT variants (Phase 6), and Idea 29 (reductions compose and preserve membership in P, but only when they are total and answer-preserving).

## 7. Failure modes this idea catches

* **Special or easier problem** (error family 5 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). Solving SAT on a promise (`trivial_promise_solver`) is not solving SAT (`trivial_solver_wrong`, `promise_correct_not_total`).
* **Invalid reduction** (error family 4). A map that leaves some input outside the promise does not transfer correctness (`composition_works_iff`).
* **Nondeterminism/randomness confusion** (error family 9). Valiant–Vazirani is randomized. Treating it as deterministic turns NP = RP into a false claim of P = NP.
* **Circular reasoning** (error family 12). Building the isolation map from a SAT decider (`decider_meets_isolation`) is circular.
* **Hidden exponential work** (error family 2). A map into the promise that internally searches for solutions hides exponential time. `compose_cost` makes the cost of `f` explicit.
* **Contradicting known results** (error family 18). A claimed polynomial-time Unique-SAT solver plus the Valiant–Vazirani reduction would give NP = RP. Such a claim must be checked against that consequence.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea32.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea32.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
