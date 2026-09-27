# Idea 25 — Decomposable constraints (component splitting)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

If the clauses of a CNF split into groups with disjoint variable sets, the formula is satisfiable exactly when every group is, and a satisfying assignment of the whole formula is obtained by merging the groups' assignments. Both files prove this for all CNFs and for any number of components. They also prove that for every `n` the chain formula is connected, so the lemma cannot be applied to it. Splitting speeds up SAT only when every component is small. The hard families known from proof complexity are connected and have linear treewidth, so on its own this idea gives no polynomial algorithm.

## 1. The idea at full strength

The hope, in the direction **P = NP**: "divide and conquer on the constraint structure". Take a CNF, find independent sub-problems, solve each one separately, and combine the answers. If every instance, perhaps after some preprocessing, fell apart into components of logarithmic size, brute force on each component would cost `2^{O(log n)} = poly(n)`, and SAT would be in P.

Issue #532 motivates this in Part I, item 1 ("Restricting geometry, connectivity, or structure collapses hardness. Hardness arises from **combinatorial freedom**") and in Part II, Phase 6 ("restricted SAT variants" as training grounds). The strongest version of the idea claims that the "combinatorial freedom" behind hardness can always be removed by decomposition.

A more general form replaces "disjoint components" with "components joined through small interfaces". That form is Idea 26 (separators) and treewidth dynamic programming. This dossier covers the exact disjoint case and shows why it cannot carry the general problem.

## 2. Precise mathematical formulation

* A literal is a pair `(var, pos)` with `var : Nat` and `pos : Bool`. A clause is a list of literals, and a CNF is a list of clauses. An assignment is a function `Nat → Bool`.
* `evalLit a (v, true) = a v` and `evalLit a (v, false) = ¬ a v`. A clause is true when some literal is true. A CNF is true when all its clauses are true. `Satisfiable φ` means `∃ a, evalCNF a φ = true`.
* `vars φ` is the list of variable occurrences of `φ`.
* `Disjoint φ ψ` means `∀ v, v ∈ vars φ → v ∉ vars ψ`.
* For a list of components `φ₁, …, φ_m`, `DisjointChain` requires each `φᵢ` to be disjoint from the concatenation of `φᵢ₊₁, …, φ_m`. This is equivalent to pairwise disjointness.

The full-strength claim would be:

> (FS) There is a polynomial-time transformation mapping every CNF `φ` to an equisatisfiable CNF whose primal graph has only connected components of size `O(log |φ|)`.

(FS) implies SAT ∈ P. The theorems below show that splitting itself is exact. They also show that the chain formula admits no non-trivial split, for every `n`. The literature cited in Section 5 shows that the hard families have no small components and no small treewidth.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `evalCNF_append` | `evalCNF a (φ ++ ψ) = evalCNF a φ && evalCNF a ψ` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `vars_append` | `vars (φ ++ ψ) = vars φ ++ vars ψ` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `evalClause_congr` | Assignments that agree on a clause's variables give the clause the same value | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `eval_congr` | Assignments that agree on `vars φ` give `φ` the same value (for all `φ`) | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `merge_left`, `merge_right` | The merged assignment evaluates `φ₁` like `a₁`, and, when the parts are disjoint, evaluates `φ₂` like `a₂` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `split_sat_iff` | If `Disjoint φ₁ φ₂`, then `Satisfiable (φ₁ ++ φ₂) ↔ Satisfiable φ₁ ∧ Satisfiable φ₂` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `sat_append_left` | `Satisfiable (φ₁ ++ φ₂) → Satisfiable φ₁ ∧ Satisfiable φ₂`, with no hypothesis | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `joinAll_sat_iff` | If `DisjointChain φs`, the concatenation is satisfiable iff every `φ ∈ φs` is satisfiable | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `chain_satisfiable`, `chain_length` | For all `n`, `chain n` (clauses `xᵢ ∨ xᵢ₊₁`, `i < n`) is satisfiable and has `n` clauses | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `adjacent_change` | If `p i ≠ p (i+d)`, then `p k ≠ p (k+1)` for some `k` with `i ≤ k` and `k+1 ≤ i+d` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `chain_not_splittable` | For all `n` and every selection `p` of clause indices that contains some `i < n` and misses some `j < n`, there is `k` with `k+1 < n` such that `p k ≠ p (k+1)` and `x_{k+1}` occurs in both `chainClause k` and `chainClause (k+1)` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `split_cost` | `2^a + 2^b ≤ 2·2^{max(a,b)}` and `2^{max(a,b)} ≤ 2^a + 2^b` | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |
| `component_obligation_splits` | Under `ComponentObligation`, `Satisfiable φ` iff every (small) component of `f φ` is satisfiable | [Idea25.lean](../lean/Idea25.lean) | [Idea25.v](../rocq/Idea25.v) |

Neither file uses axioms or unfinished proofs. The Rocq file decides membership in the merge with `in_dec Nat.eq_dec`, and the Lean file uses the decidable `v ∈ vars φ₁`. Both are constructive.

## 4. Complete argument

**Locality (`eval_congr`).** By induction on the clause, a clause's value depends only on `a` at the clause's variables: the head literal's value is `a (var l)` or its negation, and the tail is covered by the induction hypothesis. A second induction, on the list of clauses, gives the same statement for the CNF.

**Splitting (`split_sat_iff`).**

* (⇒) `evalCNF a (φ₁ ++ φ₂) = evalCNF a φ₁ && evalCNF a φ₂`, so the same `a` satisfies both parts. This direction needs no disjointness (`sat_append_left`).
* (⇐) Let `a₁ ⊨ φ₁` and `a₂ ⊨ φ₂`. Define `c v = if v ∈ vars φ₁ then a₁ v else a₂ v`. On `vars φ₁`, `c` agrees with `a₁`, so `c ⊨ φ₁` by locality. On `vars φ₂`, disjointness gives `v ∉ vars φ₁`, so `c` agrees with `a₂` and `c ⊨ φ₂`. By `evalCNF_append`, `c ⊨ φ₁ ++ φ₂`.

**Many components (`joinAll_sat_iff`).** Induct on the list of components. Apply `split_sat_iff` to the head and the concatenation of the rest, then use the induction hypothesis.

**Connectedness of the chain (`chain_not_splittable`).** A split of the clause list into two parts is described by a Boolean selection `p` on clause indices. If the split is non-trivial, `p i = true` and `p j = false` for some `i, j < n`. Assume `i < j`; the other case is symmetric. The discrete intermediate value theorem (`adjacent_change`, by induction on `d = j − i`) gives an index `k` with `i ≤ k < k+1 ≤ j < n` and `p k ≠ p (k+1)`. The clauses `xₖ ∨ xₖ₊₁` and `xₖ₊₁ ∨ xₖ₊₂` both contain `xₖ₊₁`, so the two parts share a variable and `Disjoint` fails. Every non-trivial split is caught, not only prefix/suffix splits.

**Worked example.** Take `n = 4`, so the clauses are `C₀ = x₀∨x₁`, `C₁ = x₁∨x₂`, `C₂ = x₂∨x₃` and `C₃ = x₃∨x₄`. Select `{C₀, C₂}` and leave out `{C₁, C₃}`. A witness for the theorem is `k = 0`, since `p 0 = true`, `p 1 = false` and `x₁` is shared. Every one of the `2⁴ − 2 = 14` non-trivial selections is caught the same way.

**Cost accounting (`split_cost`).** Brute force on components of sizes `a` and `b` costs about `2^a + 2^b` instead of `2^{a+b}`. That is a large saving, but it is still at least `2^{max(a,b)}`. Splitting therefore helps only if the *largest* component is small. When a component has linear size, the cost stays exponential.

**Why this is not a route to SAT ∈ P.** The splitting lemma is exact, so the obstruction is structural, not logical:

1. The chain family shows that even trivially satisfiable formulas are connected for every `n`. Connectedness alone says nothing about hardness.
2. Hard instances are connected in a strong sense. Random 3-CNF with a linear number of clauses and Tseitin formulas on constant-degree expanders have primal graphs with linear treewidth. This is a standard consequence of their expansion, not one of the formalized results. Their largest component is the whole formula.
3. The natural generalization is dynamic programming over a tree decomposition. It runs in time `2^{O(tw)} · poly(n)`, which is polynomial only for `tw = O(log n)`. A polynomial-time map from every CNF to an equisatisfiable CNF of logarithmic treewidth would put SAT in P. That is a restatement of the problem, not progress on it.

## 5. Known results and literature

* V. Chvátal and E. Szemerédi, "Many hard examples for resolution", *Journal of the ACM* 35(4), 1988. Random `k`-CNF with a suitable linear number of clauses needs exponential-size resolution refutations.
* A. Urquhart, "Hard examples for resolution", *Journal of the ACM* 34(1), 1987. Tseitin formulas on expander graphs need exponential-size resolution refutations.
* B. Courcelle, "The monadic second-order logic of graphs I: Recognizable sets of finite graphs", *Information and Computation* 85(1), 1990. MSO-definable properties are decidable in linear time on graphs of bounded treewidth. It is a central general source of fixed-parameter tractability in treewidth; the linear-time bound also uses Bodlaender's algorithm for computing tree decompositions.
* M. Alekhnovich and A. Razborov, "Satisfiability, branch-width and Tseitin tautologies", FOCS 2002 (journal version in *Computational Complexity*, 2011). SAT algorithms parameterized by branch-width, and lower bounds for Tseitin tautologies.
* M. Samer and S. Szeider, "Algorithms for propositional model counting", *Journal of Discrete Algorithms* 8(1), 2010. `#SAT` in time `2^{O(tw)}·poly` for primal treewidth `tw`.
* R. Impagliazzo and R. Paturi, "On the complexity of k-SAT", *Journal of Computer and System Sciences* 62(2), 2001. This paper introduces the Exponential Time Hypothesis (ETH).

None of these results are formalized here. The two files formalize only the exact splitting lemma, its many-component version, the connectivity of the chain family and the cost inequality.

## 6. How far the idea can be pushed toward P vs NP

At full potential the idea is the treewidth/branch-width dynamic-programming paradigm. It is exact, and it is polynomial exactly on instance families with logarithmic width. The formal content here is the base case of that paradigm: width 0 across components, meaning disjoint interfaces.

The remaining obligation for a P = NP route is (FS) from Section 2, stated in both files with the time class and the width bound `w` as parameters:

```lean
def ComponentObligation (PolyTime : (CNF → List CNF) → Prop) (w : Nat → Nat) : Prop :=
  ∃ f : CNF → List CNF, PolyTime f ∧ ∀ φ, DisjointChain (f φ) ∧
    (∀ ψ, ψ ∈ f φ → (vars ψ).length ≤ w φ.length) ∧
    (Satisfiable φ ↔ Satisfiable (joinAll (f φ)))
```

`component_obligation_splits` proves the conditional step: under the obligation, `Satisfiable φ` holds iff every component of `f φ` is satisfiable, so brute force costs at most `|f φ| · 2^{w(|φ|)}` evaluations. That cost count is informal; it is not part of the formal statement. With `w = O(log n)` and `f` polynomial, that is polynomial. In words, every CNF can be mapped in polynomial time to an equisatisfiable CNF with small components, or, more generally, with small interfaces. This obligation is **at least as strong as SAT ∈ P**. Given such a map, one runs the componentwise brute force. Conversely, if SAT ∈ P, one can output a constant-size equivalent formula. So, for an honest `PolyTime` and `w = O(log n)`, the obligation is equivalent to SAT ∈ P, hence to P = NP by Cook–Levin. Neither the machine model nor this equivalence is formalized.

Barriers:

* **Proof complexity:** a DPLL/resolution-style splitting algorithm yields resolution refutations of unsatisfiable inputs. Chvátal–Szemerédi and Urquhart give exponential lower bounds for random CNFs and expander Tseitin formulas, so any splitting algorithm that stays inside resolution takes exponential time on them.
* **ETH evidence:** if ETH holds, 3-SAT has no `2^{o(n)}` algorithm, so no polynomial-time preprocessing can shrink the width to `o(n)` in general.

Nothing here separates P from NP. The idea is a correct tool that is insufficient alone.

## 7. Failure modes this idea catches

* **"The instance splits, so it is easy."** Check the size of the largest component. `split_cost` shows that the cost is at least `2^{max component}`.
* **Assuming decomposition without proving disjointness.** `split_sat_iff` needs `Disjoint`. Without it the merge is unsound; Idea 26 gives the countermodel `[[x]]`, `[[¬x]]`. This is error family 6 (local or greedy consistency in place of global) in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).
* **Special-case reasoning** (error family 5). An algorithm for decomposable instances solves a restricted problem. `chain_not_splittable` shows that connectivity holds even in trivial families, so a proof that assumes decomposability does not cover general SAT.
* **Hidden exponential work** (error family 2). A "decomposition" whose computation or component size is not bounded moves the exponential cost elsewhere.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea25.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea25.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
