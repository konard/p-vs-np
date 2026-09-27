# Idea 02 — Certificate search (black-box search and its query lower bound)

**Verdict:** Refuted as a route (general theorem)

Any procedure that learns about a formula only by *trying candidate
certificates* (evaluating the formula on chosen assignments) needs `2^n` trials
in the worst case on `n` variables. This holds even when each trial is chosen
adaptively from the earlier answers, and it holds for CNF formulas and not only
for arbitrary predicates. Both statements are machine-checked for every `n`, and
the bound is tight. "Search smarter among certificates" is therefore refuted as a
route to P = NP. Any polynomial algorithm must read and exploit the *text* of the
formula (white-box access). That is the remaining obligation, and it is the full
P vs NP problem.

## 1. The idea at full strength

Ambitious version (direction P = NP): SAT is "just search". A satisfying
assignment is a short certificate that is easy to check (Idea 03). So a clever
enough strategy for *choosing which certificates to try*, using feedback from
failed trials, should find a witness, or conclude that none exists, after
polynomially many trials. A weaker hope is that a few failed trials can already
certify unsatisfiability.

Source in issue #532: Part I item 2 ("Local optimization can't guarantee global
optimality … Failure of known heuristics ≠ impossibility of all methods"), Part I
item 7 ("NP-hardness tells us **where structure fails**"), and Part II Phase 2
("Formalize barriers — Relativization (Baker–Gill–Solovay) … Each becomes a
**machine-checked no-go zone**"). The black-box bound proved here is exactly the
combinatorial core of the relativization barrier. Part II Phase 4 ("Attempt
formal proofs → record exact failure points") asks for the precise failure
point, which is `no_shallow_decision_tree`.

## 2. Precise mathematical formulation

* **Search problem.** For `f : List Bool → Bool` and a length `n`, the question
  is `∃ x, x.length = n ∧ f x = true`.
* **Query algorithms.** An adaptive query algorithm is a decision tree
  ```lean
  inductive DTree
    | leaf (answer : Bool)
    | query (v : List Bool) (ifFalse ifTrue : DTree)
  ```
  `t.eval f` walks the tree: at `query v t₀ t₁` it asks `f v` and continues in
  `t₁` if the answer is `true` and in `t₀` otherwise. `depth` is the largest
  number of queries on a root-to-leaf path. Every deterministic algorithm that
  touches `f` only through evaluations and makes at most `d` of them is
  described by a tree of depth `≤ d` (unfold its computation on all answer
  sequences). Its internal running time is not bounded or counted; only queries
  are.
* **Correctness.** `DecidesSearch n t :⇔ ∀ f, t.eval f = true ↔ ∃ x, x.length = n ∧ f x = true`.
* **CNF black boxes.** `oracle φ v := evalCNF (toAssign v) φ`. A tree decides
  CNF-SAT on `n` variables as a black box iff
  `∀ φ, VarsBelow n φ → (t.eval (oracle φ) = true ↔ Satisfiable φ)`.
* **Point formulas.** `pointCNF [b₀,…,b_{n−1}]` has the unit clauses
  `x_i = b_i` for `i < n`. It is built recursively as
  `[⟨0,b₀⟩] :: shiftCNF (pointCNF rest)`.
* **Claims needed by the route.** A black-box route to P = NP would need trees
  of depth `poly(n)` satisfying the CNF black-box specification for every `n`.
  The theorems below show that the minimum depth is exactly `2^n`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `length_allAssignments`, `mem_allAssignments_iff`, `nodup_allAssignments` | The list of all length-`n` vectors has length `2^n`, contains exactly the length-`n` vectors, and has no duplicates. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `pigeonhole` | If `L` has no duplicates and every element of `L` lies in `Q`, then `L.length ≤ Q.length`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `exists_unqueried` | For every `n` and every list `Q` with `Q.length < 2^n` there is `a` of length `n` with `a ∉ Q`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `nonadaptive_indistinguishable` | If `Q.length < 2^n`, there is `a` of length `n` such that the indicator of `a` has a length-`n` witness, yet it agrees with the all-false predicate on every point of `Q`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `falsePath_length_le` | The all-false path of a tree has at most `depth t` queries. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `eval_eq_of_false_on_path` | Two predicates that are false on every query of the all-false path get the same answer from the tree. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `no_shallow_decision_tree` | For every `n`, no decision tree of depth `< 2^n` satisfies `DecidesSearch n`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `linearTree_decides`, `linearTree_depth` | The tree that queries all length-`n` vectors in order decides search and has depth exactly `2^n` (the lower bound is tight). | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `pointCNF_varsBelow` | `pointCNF a` only uses variables `< a.length`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `pointCNF_iff` | For `v.length = a.length`: `v` satisfies `pointCNF a` iff `v = a`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `pointCNF_satisfiable` | Every `pointCNF a` is satisfiable. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `failed_trials_do_not_certify` | For every `n` and every list `Q` of fewer than `2^n` trial vectors (of any lengths) there is a satisfiable CNF on variables `< n` that is false on every trial in `Q`. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |
| `no_shallow_cnf_blackbox` | For every `n`, no decision tree of depth `< 2^n` decides satisfiability of all CNFs on variables `< n` when it may only evaluate the CNF on assignments. | [Idea02.lean](../lean/Idea02.lean) | [Idea02.v](../rocq/Idea02.v) |

Not machine-checked: the relativization theorem of Baker–Gill–Solovay, the
quantum `Ω(√(2^n))` lower bound, and any statement about algorithms that read
the formula text. The theorems count *queries only*, which is the standard
measure in query complexity.

## 4. Complete argument

**Counting.** `allAssignments n` lists all length-`n` vectors without
duplicates and has length `2^n` (proved by induction as in Idea 01).

**Pigeonhole.** By induction on `L`. The empty case is trivial. For `x :: L`
with `x ∉ L` and `x :: L ⊆ Q`, remove one occurrence of `x` from `Q`, giving
`Q'` of length `|Q| − 1`. (Lean uses `List.erase`, Rocq uses `in_split`.)
Every `y ∈ L` differs from `x`, so `y ∈ Q'`. By induction `|L| ≤ |Q'|`, hence
`|x :: L| ≤ |Q|`.

**Unqueried point.** If every length-`n` vector were in `Q`, then pigeonhole
applied to `allAssignments n ⊆ Q` would give `2^n ≤ |Q|`, a contradiction.

**Adaptive lower bound.** Let `t` have depth `< 2^n`. Follow the path taken
when every answer is `false`. It asks at most `depth t < 2^n` questions, the
list `falsePath t`. Choose `a` of length `n` not on that list. The indicator
`1_a` and the all-false predicate `0` both answer `false` on every query of the
path, so the tree follows the same path for both and gives the same answer
(`eval_eq_of_false_on_path`, by induction on the tree). But `1_a` has a witness
and `0` does not, so a correct tree would have to answer `true` for one and
`false` for the other. This is the classical adversary argument: the adversary
answers "no" until the algorithm stops, and only then decides where the witness
is.

**Tightness.** `linearTree [v₁,…,v_N]` asks `v₁`. It answers `true` if the
answer is yes and otherwise continues with the rest, ending in `leaf false`. It
decides search when the list is `allAssignments n`, and its depth is `N = 2^n`.

**Transfer to CNFs.** The adversary must be realized by *formulas*.
`pointCNF a` is the conjunction of the unit clauses `x_i = a_i`. For vectors of
the right length it is satisfied exactly by `a` (`pointCNF_iff`, by induction on
`a`, using `evalCNF_shift` to peel off variable 0). Trial vectors in the CNF
setting may have any length, so each trial `v` is normalised to
`norm v = prefixOf (toAssign v) n`, its first `n` bits padded with `false`. Since
`pointCNF a` only uses variables `< n`, `evalCNF (toAssign v)` and
`evalCNF (toAssign (norm v))` agree on it (`evalCNF_congr`). Choose `a` not
among the fewer than `2^n` normalised trials. Then `pointCNF a` is satisfiable
but false on every trial (`failed_trials_do_not_certify`). For a tree of depth
`< 2^n`, take `Q = falsePath t`. The formula `pointCNF a` and the unsatisfiable
formula `[[]]` (one empty clause) both answer `false` on the whole path, so the
tree cannot separate them (`no_shallow_cnf_blackbox`).

**Worked numbers.** For `n = 30`, any black-box procedure needs
`2^30 = 1 073 741 824` trials in the worst case. For `n = 100` it needs about
`1.27·10^30`. A procedure that stops after `10^9` failed trials on 30 variables
and declares "unsatisfiable" is wrong on at least one of the formulas
`pointCNF a`.

**Why this refutes the route and not P vs NP.** The hard instances
`pointCNF a` are trivial when their *text* is read: the unit clauses spell out
`a`. The lower bound comes only from forbidding the algorithm to look at the
formula. P vs NP concerns algorithms that read the whole input, and the theorem
says nothing about them.

## 5. Known results and literature

* T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question",
  *SIAM Journal on Computing* 4(4), 1975. There are oracles `A` with
  `P^A = NP^A` and oracles `B` with `P^B ≠ NP^B`. The construction of `B` is a
  diagonalization against polynomial-time oracle machines built on the same
  adversary argument as `no_shallow_decision_tree`. (Not formalized here.)
* L. K. Grover, "A fast quantum mechanical algorithm for database search",
  *Proc. 28th ACM STOC*, 1996. Quantum black-box search with `O(√N)` queries.
  (Not formalized.)
* C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and
  weaknesses of quantum computing", *SIAM Journal on Computing* 26(5), 1997.
  Quantum black-box search needs `Ω(√N)` queries, so Grover is optimal and even
  quantum black-box search over `2^n` certificates takes `2^{n/2}` queries.
  (Not formalized.)
* The deterministic `N`-query lower bound for search/OR is folklore in query
  (decision-tree) complexity. The version formalized here is the adaptive one.

## 6. How far the idea can be pushed toward P vs NP

At full potential the idea gives:

1. an exact answer for black-box certificate search: the deterministic query
   complexity is exactly `2^n` (`no_shallow_decision_tree` and
   `linearTree_depth`), even when restricted to CNF black boxes
   (`no_shallow_cnf_blackbox`);
2. a proof that no number of failed trials below `2^n` certifies
   unsatisfiability (`failed_trials_do_not_certify`), which is the formal core
   of "absence of evidence found by search is not a proof of absence".

**Remaining obligation.** The route itself is closed. What remains is
"exploit formula structure": a polynomial algorithm must use the syntax of `φ`
and not just its values. No Lean `def` is introduced for it in this file,
because it is literally Idea 01's `PolySATDecider`, which is equivalent to
P = NP by Cook–Levin.

**Barriers.** The theorem is a *relativizing* statement: it holds relative to
every oracle, since the predicate is an oracle. Baker–Gill–Solovay show that any
argument of this relativizing kind cannot settle P vs NP in either direction.
So the query bound can never be turned into P ≠ NP. Real formulas are not
oracles, and the lower bound disappears once the formula is readable, as the
`pointCNF` instances show. Proof-complexity and circuit lower bounds are the
known non-relativizing substitutes, and they meet their own barriers (natural
proofs, algebrization).

**Strength.** The refutation covers every deterministic black-box algorithm.
Randomized black-box algorithms also need `Ω(2^n)` queries and quantum ones need
`Ω(2^{n/2})`, but these are cited and not formalized.

## 7. Failure modes this idea catches

* **Failed search treated as proof of unsatisfiability**
  ([error family 15](../../../attempts/COMMON_ERRORS.md#15-confusing-verification-search-construction-and-certificates)):
  `failed_trials_do_not_certify` gives an explicit satisfiable counterexample
  for any list of fewer than `2^n` trials.
* **Heuristic or sampling "evidence"**
  ([family 8](../../../attempts/COMMON_ERRORS.md#8-treating-heuristics-experiments-or-probability-as-proof)):
  sampling polynomially many assignments is a shallow tree. It cannot
  distinguish `pointCNF a` from an unsatisfiable formula.
* **Quantum or physical "parallel search"**
  ([family 9](../../../attempts/COMMON_ERRORS.md#9-confusing-nondeterminism-randomness-quantum-choice-or-physical-process)):
  black-box search stays exponential (`2^{n/2}` quantum, by BBBV).
* **Barrier-limited techniques**
  ([family 14](../../../attempts/COMMON_ERRORS.md#14-ignoring-known-barriers-or-using-a-barrier-limited-technique)):
  a P ≠ NP "proof" whose only ingredient is an adversary argument against
  query algorithms relativizes and is therefore insufficient.
* **Hidden exponential work**
  ([family 2](../../../attempts/COMMON_ERRORS.md#2-hiding-exponential-work-in-a-claimed-polynomial-algorithm)):
  an algorithm that is "polynomial per trial" but has no stated bound on the
  number of trials needs `2^n` trials in the worst case.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea02.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea02.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea02.{vo,vok,vos,glob}` and
`.Idea02.aux` files.
