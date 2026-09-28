# Idea 26 — Separator consistency

**Verdict:** Refuted as a route (general theorem)

The idea is to split a CNF into two sides that share only a small set `S` of separator variables, solve each side, and combine the results. This is exact only if the two sides are matched on a *common separator state*, which is an assignment to `S`. The files prove this exact separator theorem for all CNFs. They prove, for every variable, that the naive variant (check each side separately and glue) is unsound. They also prove that the `2^|S|` separator states cannot be merged: any procedure that summarises one side and decides from the summary must tell all of them apart (the equality gadget). That is a lower bound of `2^|S|` summary values, i.e. `|S|` bits, not an exponential lower bound on the combination step. The exact method enumerates all `2^|S|` states, so on formulas all of whose balanced separators have linear size, which include the standard hard families (cited, not formalized), it costs `2^{Ω(n)}`. As a polynomial method for general SAT, this route is refuted: the naive variant by a formal theorem, the exact state-enumerating variant on the hard families by the cited separator facts. In the Lean file the recursive route is stated in the shared machine model. The open obligation `SATSeparatorReduction` asks for a `Complexity.Machine` that maps every SAT instance, within a polynomial number of `Run` steps, to an equisatisfiable instance with a recursive separator decomposition of logarithmic budget. `pEqualsNP_of_separatorReduction` derives `PEqualsNP` from it, given two known theorems that are not mechanised: `SATHard` and `LogSeparatorSATInP` (separator-state dynamic programming is polynomial at logarithmic treewidth). The obligation is as hard as P = NP.

## 1. The idea at full strength

The hope, in the direction **P = NP**: find a small "interface" `S` between two halves of a formula. Solve each half with only a little information about the interface, and recurse. If every formula had separators of size `O(log n)` at every level of the recursion, and the halves could be combined cheaply, SAT would be solvable in polynomial time.

A naive variant hopes that it is enough to check each half's satisfiability *separately* and "glue" the results.

In issue #532 this belongs to Part I, item 1 ("Restricting geometry, connectivity, or structure collapses hardness") and item 2 ("We don't know whether a different global invariant exists"). The separator state is the most natural candidate for a "global invariant" assembled from local pieces. Idea 25 is the special case `S = ∅`.

## 2. Precise mathematical formulation

The CNF model is the one used in Idea 25: literals `(var, pos)`, clauses as lists, CNFs as lists, and assignments `Nat → Bool`.

* A **separator** for `A ++ B` is a list `S` with `∀ v, v ∈ vars A → v ∈ vars B → v ∈ S`.
* A **separator state** is a Boolean vector `σ` with `|σ| = |S|`. The state of an assignment `a` is `restrict S a = S.map a`.
* `allBool n` enumerates all Boolean vectors of length `n`, `false`-first.
* `units S σ` is the CNF `[[S₀ = σ₀], [S₁ = σ₁], …]` made of unit clauses. It forces the separator to take state `σ`.

The claims needed for a polynomial separator algorithm are:

> (Sep) For every CNF, a polynomial-time recursive separator decomposition with separators of size `O(log n)` at every level;
> (Comb) a combination step whose cost is polynomial in `|S|`.

In the Lean file, (Sep) is stated in the shared machine model (`Machines`), where time is the `Run` step count of a `Complexity.Machine`. A recursive decomposition with a total separator budget `r` along every branch is

```lean
inductive SepTree : Nat → CNF → Prop
  | leaf {r : Nat} {φ : CNF} : (vars φ).length ≤ r → SepTree r φ
  | split {r : Nat} {A B : CNF} (S : List Nat) :
      (∀ v, v ∈ vars A → v ∈ vars B → v ∈ S) → S.length ≤ r →
      SepTree (r - S.length) A → SepTree (r - S.length) B → SepTree r (A ++ B)

def SepPromise (k : Nat) (w : Word) : Prop :=
  SepTree (k * Nat.log2 (w.length + 1)) (ofM (Machines.decode w))

def SeparatorReduction (L : Language) (k : Nat) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
    ∀ x, SepPromise k (f x) ∧ L x = Machines.SAT (f x)

/-- Open obligation. -/
def SATSeparatorReduction : Prop := ∃ k, SeparatorReduction Machines.SAT k

/-- Known theorem, not mechanised here. -/
def LogSeparatorSATInP : Prop :=
  ∀ k, ∃ (d : Machine) (p : Polynomial), Machines.DecidesOn d p (SepPromise k) Machines.SAT
```

`ofM` reads a CNF of the shared layer in this file's syntax, and `sat_ofM` proves that `Machines.SAT w = true` iff that CNF is satisfiable. The budget is shared along a branch, not granted afresh at each level. The bag of a node can be taken as the variables of its formula that lie in the separators on its path, plus the leaf variables at a leaf. This gives a tree decomposition of the primal graph of width below `2r` (argued in the docstring, not mechanised). A per-level bound `O(log n)` over `O(log n)` levels would allow treewidth `O(log² n)`, and the known theorem would then not be available. `LogSeparatorSATInP` is true for the budgeted form. A tree decomposition of width `O(log n)` can be found in polynomial time (Robertson–Seymour 1995; Bodlaender et al. 2016), and dynamic programming over its separator states runs in `2^{O(tw)}·poly` (Alekhnovich–Razborov 2002; Samer–Szeider 2010). No machine carrying this out is mechanised, so the statement enters only as a named hypothesis.

The earlier one-level form is kept as the schema `SeparatorObligationFor PolyTime w` over a caller-supplied class `PolyTime`. The machine model does not instantiate it naturally: the schema bounds the separator by a function of the number of clauses, while the machine promise uses the length of the encoded word, and it is recursive.

The files prove a weaker, exact statement in the one-way summary model: a sound summary must be injective on all `2^|S|` states, so it has at least `2^|S|` distinct values (`|S|` bits). This rules out merging states, but it does not by itself exclude a combination step polynomial in `|S|`. The exponential cost of the exact method comes from enumerating the states. The hard families fail (Sep): all their balanced separators have linear size (cited).

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `eval_congr` | Assignments that agree on `vars φ` evaluate `φ` equally | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `length_allBool` | `(allBool n).length = 2^n` for all `n` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `mem_allBool` | `σ ∈ allBool n ↔ σ.length = n` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `restrict_eq_agree` | Equal separator states imply agreement on every `v ∈ S` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `separator_sat_iff` | If all shared variables of `A`, `B` lie in `S`, then `Satisfiable (A ++ B)` iff some `σ ∈ allBool |S|` has a model of `A` with state `σ` and a model of `B` with state `σ` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `separate_not_joint` | For every variable `x`, `[[x]]` and `[[¬x]]` are each satisfiable, but `[[x]] ++ [[¬x]]` is not | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `units_eval` | For `|σ| = |S|`: `a ⊨ units S σ ↔ restrict S a = σ` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `realizable` | If `S` is duplicate-free, every `σ` with `|σ| = |S|` is `restrict S a` for some `a` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `compatible_states_units` | If `S` is duplicate-free and `|σ| = |S|`: some model of `units S σ` has state `τ` iff `τ = σ` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `equality_gadget` | If `S` is duplicate-free and `|σ| = |τ| = |S|`: both `units S σ` and `units S τ` are satisfiable, and `units S σ ++ units S τ` is satisfiable iff `σ = τ` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `summary_must_be_injective` | Let `S` be duplicate-free, and let `D (summ σ) τ` decide `Satisfiable (units S σ ++ units S τ)` correctly for all length-`|S|` states. Then `summ σ = summ τ` implies `σ = τ` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `SeparatorObligationFor` (def) | One-level schema for (Sep) over a free class `PolyTime` of maps and a bound `w` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `separator_obligation_states` | Under `SeparatorObligationFor`, `Satisfiable φ` iff some of the `2^{|S|}` separator states (`|S| ≤ w(|φ|)`) is realized by models of both sides | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `SepTree` (inductive) | Recursive separator decomposition with a total separator budget `r` along every branch | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `sepTree_root` | A separator tree is a leaf with at most `r` variable occurrences, or one exact separator step (`separator_sat_iff`) with `|S| ≤ r` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `sepTree_mono` | A separator tree with budget `r` has every budget `r' ≥ r` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `sat_ofM` | `Machines.SAT w = true ↔ Satisfiable (ofM (Machines.decode w))` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `SepPromise`, `SeparatorReduction` (defs) | The logarithmic-budget promise on words, and a polynomial-time machine reduction onto it | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `LogSeparatorSATInP` (def) | Known theorem, not mechanised: for each `k`, a polynomial-time machine decides SAT on `SepPromise k`. Used only as a hypothesis | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `SATSeparatorReduction` (def) | Open obligation: `∃ k, SeparatorReduction Machines.SAT k` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `inP_of_separatorReduction` | `LogSeparatorSATInP → SeparatorReduction L k → InP L` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `inP_sat_of_separatorReduction` | `LogSeparatorSATInP → SATSeparatorReduction → InP Machines.SAT` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `pEqualsNP_of_separatorReduction` | `SATHard → LogSeparatorSATInP → SATSeparatorReduction → PEqualsNP` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `separatorReduction_states` | Under the obligation, each reduced instance is a small leaf or splits exactly over at most `2^{k·log₂(|f x|+1)}` separator states, and `SAT x` is its satisfiability | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `exists_not_reducible` | For every `M`, some language has no machine map `f` with `L x = M (f x)` (Cantor over machines) | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |
| `not_forall_separatorReduction` | Non-vacuity: `¬ ∀ L, SeparatorReduction L k` for every `k` | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |

The rows from `SepTree` on have the same names in Rocq, with two Rocq-specific differences. The constructors of the inductive `SepTree` are `SepTree_leaf` and `SepTree_split` (Lean: `SepTree.leaf`, `SepTree.split`), and `SeparatorObligationFor` destructs the separator triple with `let '(A, B, Sep) := f phi` instead of Lean projections. In Rocq, `exists_not_reducible` is proved by a pointwise constructive diagonal: the helper `viaMachine` runs a (machine, polynomial) pair with the computable step-bounded `runOut` and reads the output with `readBits` (Lean's `viaMachine M m` takes the machine alone and is noncomputable), `viaMachine_eq` shows that it agrees with `M (f x)` pointwise (Lean states a function equality), and no function extensionality or excluded middle is needed. Implicit Lean arguments are explicit `forall`s in Rocq. Neither file uses axioms.

No axioms are used, and there is no `sorry`/`Admitted`.

## 4. Complete argument

**Separator theorem (`separator_sat_iff`).**

* (⇒) If `a ⊨ A ++ B`, take `σ = restrict S a`. It has length `|S|`, so `σ ∈ allBool |S|`, and `a` itself witnesses both sides.
* (⇐) Let `a ⊨ A` and `b ⊨ B` with `restrict S a = restrict S b = σ`. Then `a v = b v` for all `v ∈ S` (`restrict_eq_agree`). Define `c v = if v ∈ vars A then a v else b v`. By locality, `c ⊨ A`. For `v ∈ vars B`: if also `v ∈ vars A`, then `v ∈ S`, so `c v = a v = b v`; otherwise `c v = b v`. So `c ⊨ B`, and hence `c ⊨ A ++ B`.

The theorem turns the global question into a *disjunction over `2^|S|` states*. That gives the exact dynamic programme: for each state, check both sides.

**Agreement is essential (`separate_not_joint`).** With `A = [[x]]` and `B = [[¬x]]` (`S = [x]`), each side is satisfiable, but no state `σ ∈ {[false], [true]}` is compatible with both. A procedure that checks each side separately and ignores the separator would answer "satisfiable", which is wrong. This holds for every variable `x`.

**All states are needed (`equality_gadget`, `summary_must_be_injective`).** Fix a duplicate-free `S`.

* `units_eval` shows, by induction on `S`, that `a ⊨ units S σ` exactly when `restrict S a = σ`.
* `realizable` builds, by induction on `S`, an assignment with any prescribed state. The update at the head `s` does not disturb the tail because `s ∉ tail`.
* Together these give that `units S σ` is satisfiable, and that `units S σ ++ units S τ` is satisfiable iff `σ = τ`.

Now let a procedure compress the left side `units S σ` to `summ σ`, and decide the union from `summ σ` and the right state `τ` using some `D`. Suppose `summ σ = summ τ`. Since `σ = σ`, `D (summ σ) σ = true`. Then `D (summ τ) σ = true`, so `units S τ ++ units S σ` is satisfiable, and `τ = σ`. The summary map is therefore injective on the `2^|S|` states. In other words, the separator interface carries the full Equality function on `|S|` bits.

**Cost.** The exact separator algorithm runs through `2^|S|` states and solves two constrained subproblems for each. Recursively, with separators of size `s(n)`, the running time is `2^{O(s(n))}` per level times the subproblem cost. It is polynomial only when `s(n) = O(log n)` at every level.

**Worked numbers.** For `|S| = 1`: 2 states, and the gadget pair is `([true], [false])`, which is exactly `separate_not_joint`. For `|S| = 20`: 1,048,576 states, all pairwise distinguished by the gadget. For a 3-regular expander on `n` vertices every balanced separator has `Ω(n)` vertices (cited). If, say, every balanced separator of the primal graph has at least 100 vertices, the exact method must handle at least `2^{100}` states at the top level.

**Why this refutes the route.** A polynomial-time separator algorithm needs (Sep) and (Comb). `summary_must_be_injective` shows that no sound one-way summary has fewer than `2^|S|` values, so states cannot be merged; this is an `|S|`-bit lower bound on the interface, not an exponential lower bound on (Comb). (Sep) fails for the hard families: in Tseitin formulas on expanders, and with high probability in random 3-CNF, every balanced separator of the primal graph has linear size (Section 5; not formalized). The exact state-enumerating method therefore takes `2^{Ω(n)}` time on these families. This does not exclude other algorithms, since any other algorithm is a different idea.

## 5. Known results and literature

* R. J. Lipton and R. E. Tarjan, "A separator theorem for planar graphs", *SIAM Journal on Applied Mathematics* 36(2), 1979. Planar graphs have balanced separators of size `O(√n)`.
* R. J. Lipton and R. E. Tarjan, "Applications of a planar separator theorem", *SIAM Journal on Computing* 9(3), 1980. Divide and conquer with separators, giving `2^{O(√n)}` algorithms for several NP-complete planar problems.
* D. Lichtenstein, "Planar formulae and their uses", *SIAM Journal on Computing* 11(2), 1982. Planar 3-SAT is NP-complete. Combined with the separator theorem, this gives `2^{O(√n)}` algorithms for an NP-complete problem; unless P = NP, `O(√n)` separators do not by themselves give polynomial algorithms.
* S. Hoory, N. Linial and A. Wigderson, "Expander graphs and their applications", *Bulletin of the AMS* 43(4), 2006. Expanders have no sublinear balanced separators.
* A. Urquhart, "Hard examples for resolution", *Journal of the ACM* 34(1), 1987. Tseitin formulas on expanders.
* E. Ben-Sasson and A. Wigderson, "Short proofs are narrow — resolution made simple", *Journal of the ACM* 48(2), 2001. Width–size trade-off for resolution.
* A. C.-C. Yao, "Some complexity questions related to distributive computing", STOC 1979. The communication model. Equality on `k` bits needs `k` bits deterministically; the `equality_gadget` is its CNF analogue.
* E. Kushilevitz and N. Nisan, *Communication Complexity*, Cambridge University Press, 1997.

None of these theorems are formalized here. The files formalize the exact separator theorem, the enumeration of the `2^|S|` states, and the equality-gadget lower bound for one-way summaries.

## 6. How far the idea can be pushed toward P vs NP

At full potential this idea is separator/treewidth dynamic programming. Its guarantees are:

* `poly(n)` time when every level has `O(log n)` separators;
* `2^{O(√n)}` time on planar instances, which is still NP-complete by Lichtenstein;
* `2^{O(n)}` time in general.

One level of (Sep) is kept in both files as the schema `SeparatorObligationFor PolyTime w`, and `separator_obligation_states` proves its conditional step: satisfiability is decided by the `2^{w(|φ|)}` separator states (in Rocq the triple is destructured as `(A, B, Sep)`). The schema's class `PolyTime` is supplied by the caller, so it carries no running-time content.

The remaining obligation for a P = NP route is the recursive form of (Sep) in the machine model, `SATSeparatorReduction` (Section 2). The proved route is

```lean
theorem pEqualsNP_of_separatorReduction (hard : Machines.SATHard)
    (hS : LogSeparatorSATInP) (h : SATSeparatorReduction) : PEqualsNP
```

Besides the obligation it uses two known theorems that are not mechanised. `SATHard` is the hardness half of Cook–Levin (shared layer). `LogSeparatorSATInP` states that (Comb), done exactly by enumerating separator states, is polynomial at logarithmic budget, with a machine carrying it out. `separatorReduction_states` is the exact step: every reduced instance is a small leaf or splits over at most `2^{k·log₂(|f x|+1)}` separator states. `not_forall_separatorReduction` shows that the obligation is a statement about SAT: for every `k`, some language has no such reduction. The files also show that a sound one-way summary needs at least `2^|S|` values (`|S|` bits), so states cannot be merged and the budget cannot be cheated at the interface. The obligation is equivalent to SAT ∈ P (only the forward direction is mechanised). If SAT ∈ P, a machine outputs a constant-size formula, which is a leaf. So it is not easier than the original problem.

Barriers and evidence:

* **Proof complexity:** on an unsatisfiable formula, separator DP roughly corresponds to resolution-type refutations whose width is about the separator size. Urquhart's and Ben-Sasson–Wigderson's width–size bounds give `2^{Ω(n)}` for expander Tseitin formulas.
* **Communication complexity:** the equality gadget shows that the interface information cannot be compressed below `|S|` bits. That is a lower bound on the summary length, not on the number of table rows; the `2^|S|` rows are a feature of the exact method.
* **ETH evidence:** Planar 3-SAT reaches `2^{O(√n)}`, and under ETH it has no `2^{o(√n)}` algorithm. This is a known consequence of ETH plus the quadratic-size reduction to planar SAT; it is cited as background and not formalized.

This idea does not bear on P ≠ NP. It is an algorithmic method, and its failure on some families says nothing about all algorithms.

## 7. Failure modes this idea catches

* **"Both halves are satisfiable, so the whole is."** `separate_not_joint` refutes this for every variable. This is error family 6 (local or greedy consistency in place of global) in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).
* **"The interface is small, so we only need a few bits of state."** `summary_must_be_injective` shows that a sound summary must distinguish all `2^|S|` interface states. A method that enumerates them does exponential work when `|S|` is linear. This is error family 2 (hidden exponential work) and error family 7 (counting mistakes).
* **Special-case structure** (error family 5). Results for planar or bounded-treewidth inputs do not transfer to general SAT without a structure-inducing reduction, and such a reduction would itself decide SAT.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea26.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea26.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
