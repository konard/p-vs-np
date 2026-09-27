# Idea 26 — Separator consistency

**Verdict:** Refuted as a route (general theorem)

The idea is to split a CNF into two sides that share only a small set `S` of separator variables, solve each side, and combine the results. This is exact only if the two sides are matched on a *common separator state*, which is an assignment to `S`. The files prove this exact separator theorem for all CNFs. They also prove that the `2^|S|` separator states cannot be merged: any procedure that summarises one side and decides from the summary must tell all of them apart (the equality gadget). For formulas with linear-size separators, which include the standard hard families, the exact method therefore costs `2^{Ω(n)}`. As a polynomial method for general SAT, this route is refuted.

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

The files prove that (Comb) is impossible in the one-way summary model: the summary must be injective on all `2^|S|` states. The hard families fail (Sep): they have linear separators.

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
| `separator_obligation_states` | Under `SeparatorObligation`, `Satisfiable φ` iff some of the `2^{|S|}` separator states (`|S| ≤ w(|φ|)`) is realized by models of both sides | [Idea26.lean](../lean/Idea26.lean) | [Idea26.v](../rocq/Idea26.v) |

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

**Worked numbers.** For `|S| = 1`: 2 states, and the gadget pair is `([true], [false])`, which is exactly `separate_not_joint`. For `|S| = 20`: 1,048,576 states, all pairwise distinguished by the gadget. For a 3-regular expander on `n` vertices every balanced separator has `Ω(n)` vertices. With `n = 1000` and a separator of size about 100 or more, the exact method must handle at least `2^{100}` states.

**Why this refutes the route.** A polynomial-time separator algorithm needs (Sep) and (Comb). (Comb) is excluded in the one-way summary model by `summary_must_be_injective`: no sound summary with fewer than `2^|S|` values exists. (Sep) fails for the hard families: Tseitin formulas on expanders and random 3-CNF have primal graphs with linear-size balanced separators (Section 5). The route therefore gives `2^{Θ(n)}` on these families. This does not exclude other algorithms, since any other algorithm is a different idea.

## 5. Known results and literature

* R. J. Lipton and R. E. Tarjan, "A separator theorem for planar graphs", *SIAM Journal on Applied Mathematics* 36(2), 1979. Planar graphs have balanced separators of size `O(√n)`.
* R. J. Lipton and R. E. Tarjan, "Applications of a planar separator theorem", *SIAM Journal on Computing* 9(3), 1980. Divide and conquer with separators, giving `2^{O(√n)}` algorithms for several NP-complete planar problems.
* D. Lichtenstein, "Planar formulae and their uses", *SIAM Journal on Computing* 11(2), 1982. Planar 3-SAT is NP-complete. Combined with the separator theorem, this shows that even `O(√n)` separators yield only subexponential (`2^{O(√n)}`) algorithms, not polynomial ones, for an NP-complete problem.
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

One level of (Sep) is stated in both files, with the time class and the separator bound `w` as parameters:

```lean
def SeparatorObligation (PolyTime : (CNF → CNF × CNF × List Nat) → Prop) (w : Nat → Nat) :
    Prop :=
  ∃ f : CNF → CNF × CNF × List Nat, PolyTime f ∧ ∀ φ,
    (∀ v, v ∈ vars (f φ).1 → v ∈ vars (f φ).2.1 → v ∈ (f φ).2.2) ∧
    (f φ).2.2.length ≤ w φ.length ∧
    (Satisfiable φ ↔ Satisfiable ((f φ).1 ++ (f φ).2.1))
```

`separator_obligation_states` proves the conditional step: under the obligation, satisfiability is decided by the `2^{w(|φ|)}` separator states (in Rocq the triple is destructured as `(A, B, Sep)`). Applied recursively with `w = O(log n)`, this gives the polynomial DP.

The remaining obligation for a P = NP route is (Sep) together with a cheaper (Comb). The files show that (Comb) cannot be cheaper than `2^|S|` summary values in the one-way model. So the obligation reduces to: *every CNF can be transformed in polynomial time into an equisatisfiable CNF with logarithmic separators at every level*. As in Idea 25, this is equivalent to SAT ∈ P. If SAT ∈ P, output a trivial formula; conversely, run the DP. It is not easier than the original problem.

Barriers and evidence:

* **Proof complexity:** on an unsatisfiable formula, separator DP roughly corresponds to resolution-type refutations whose width is about the separator size. Urquhart's and Ben-Sasson–Wigderson's width–size bounds give `2^{Ω(n)}` for expander Tseitin formulas.
* **Communication complexity:** the equality gadget shows that the interface information cannot be compressed below `|S|` bits, so the number of table rows cannot drop below `2^|S|`.
* **ETH evidence:** Planar 3-SAT reaches `2^{O(√n)}`, and under ETH it has no `2^{o(√n)}` algorithm. This is a known consequence of ETH plus the linear-size reduction to planar SAT; it is cited as background and not formalized.

This idea does not bear on P ≠ NP. It is an algorithmic method, and its failure on some families says nothing about all algorithms.

## 7. Failure modes this idea catches

* **"Both halves are satisfiable, so the whole is."** `separate_not_joint` refutes this for every variable. This is error family 6 (local or greedy consistency in place of global) in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).
* **"The interface is small, so we only need a few bits of state."** `summary_must_be_injective` shows that the number of interface states is `2^|S|`, not `|S|`. If `|S|` is linear, that number is exponential. This is error family 2 (hidden exponential work) and error family 7 (counting mistakes).
* **Special-case structure** (error family 5). Results for planar or bounded-treewidth inputs do not transfer to general SAT without a structure-inducing reduction, and such a reduction would itself decide SAT.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea26.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea26.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
