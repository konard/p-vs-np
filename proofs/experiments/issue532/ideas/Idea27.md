# Idea 27 — Variable elimination (Davis–Putnam resolution)

**Verdict:** Refuted as a route (general theorem)

The idea is to remove variables one at a time and replace the clauses that mention a variable `v` by all their resolvents on `v`. The files prove the Davis–Putnam theorem for every CNF and every variable: `φ` is satisfiable iff `eliminate v φ` is, and `eliminate v φ` no longer mentions `v`. They also prove the exact size law `|eliminate v φ| = |rest| + |pos| · |neg|`, and give a family for every `p, q` in which `p + q` clauses become exactly `p · q` clauses. Because the procedure is a form of resolution, Haken's exponential lower bound for the pigeonhole principle shows that no elimination order is polynomial on all inputs. That final step uses Haken's theorem and the simulation of elimination runs by resolution, both cited and not formalized; the formal part is the exactness of each step and the multiplicative blow-up. Elimination is exact but not a polynomial-time route.

## 1. The idea at full strength

The hope, in the direction **P = NP**, is that existential quantification over one Boolean variable is cheap. The rule is `∃v. φ ≡ (φ with the v-clauses replaced by their resolvents)`. Applied `n` times, it would decide SAT by elimination alone. If a clever elimination order, perhaps chosen by a heuristic, always kept the clause set polynomial, SAT would be in P.

In issue #532 this is Part I, item 1 ("Restricting geometry, connectivity, or structure collapses hardness"), since elimination is polynomial when the induced width is small. It also fits item 2 ("We don't know whether a different global invariant exists"), because the eliminated formula is a candidate invariant: it has exactly the same satisfiability status. Part II, Phase 4 ("Encode proof templates ... record exact failure points") asks for exactly this treatment.

## 2. Precise mathematical formulation

The CNF model is the one shared with Ideas 25–26: literals `(var, pos)`, clauses as lists, CNFs as lists, and assignments `Nat → Bool`. For a variable `v`:

* `hasLit v b c` holds iff the literal `(v, b)` occurs in `c`, and `mentions v c` holds iff some literal of `c` has variable `v`.
* `posClauses v φ` are the clauses containing `v` but not `¬v`, and `negClauses v φ` are those containing `¬v` but not `v`.
* `restClauses v φ` are the clauses not mentioning `v`.
* `strip v c` deletes every literal on `v`, and `resolvent v c d = strip v c ++ strip v d`.
* `eliminate v φ = restClauses v φ ++ [resolvent v c d | c ∈ posClauses v φ, d ∈ negClauses v φ]`.

Clauses containing both `v` and `¬v` are tautologies. They are dropped, which is why the theorem needs no side condition. The claim needed for a polynomial algorithm is:

> (Order) For every CNF `φ` on `n` variables there is an elimination order `v₁, …, vₙ`, computable in polynomial time, such that every intermediate formula has `poly(|φ|)` clauses.

The files prove that each step is exact and measure its size exactly. Haken's theorem (cited) refutes (Order).

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `eval_congr` | Assignments that agree on `vars φ` evaluate `φ` equally | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `evalClause_iff`, `evalCNF_iff` | A clause holds iff some literal holds, and a CNF holds iff every clause holds | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `hasLit_iff`, `mentions_iff`, `mem_strip` | Specifications of the Boolean tests and of `strip` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `eliminate_no_v` | No clause of `eliminate v φ` mentions `v` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `eliminate_length` | `|eliminate v φ| = |restClauses v φ| + |posClauses v φ| · |negClauses v φ|` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `eliminate_sound` | Every model of `φ` is a model of `eliminate v φ` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `eliminate_complete` | If `b ⊨ eliminate v φ`, then `b[v := chooseVal v φ b] ⊨ φ` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `eliminate_sat_iff` | **Davis–Putnam:** `Satisfiable φ ↔ Satisfiable (eliminate v φ)` for all `v`, `φ` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `blowup_clauses` | The family `blowup p q` has `p + q` clauses | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `blowup_length` | `|eliminate x₀ (blowup p q)| = p · q` for all `p, q` | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |
| `blowup_resolvent` | Each resolvent is the two-literal clause on the two side variables | [Idea27.lean](../lean/Idea27.lean) | [Idea27.v](../rocq/Idea27.v) |

No axioms are used, and there is no `sorry`/`Admitted`. In Lean, `posSide p` uses `List.range p`; in Rocq it uses `seq 0 p`. These are the same list.

## 4. Complete argument

**Soundness (`eliminate_sound`).** Let `a ⊨ φ`. Clauses in `restClauses` are clauses of `φ`. For a resolvent of `c ∈ pos` and `d ∈ neg`, split on `a v`.

* If `a v = true`, then `d` is satisfied by some literal. It cannot be `¬v`, which is false, and it cannot be `v`, because `d` does not contain `v`. So the satisfying literal survives in `strip v d`.
* If `a v = false`, the same argument applies to `c`.

Either way the resolvent is true.

**Completeness (`eliminate_complete`).** Let `b ⊨ eliminate v φ`. Set `v` to `true` exactly when some positive clause `c` has `strip v c` false under `b`:

```
chooseVal v φ b = ¬ (∀ c ∈ pos, b ⊨ strip v c)
```

Changing `v` does not affect clauses that do not mention `v` (`update_nomention`) or stripped clauses (`update_strip`). Now check each clause `c ∈ φ`:

* `c` does not mention `v`: it is in `rest ⊆ eliminate v φ`, so it holds.
* `c` contains both `v` and `¬v`: whichever value `v` gets, one of the two literals is true (`sat_of_lit`).
* `c ∈ pos`: if `v = true`, the literal `v` satisfies it. If `v = false`, then by the choice every `strip v c'` with `c' ∈ pos` is true, in particular `strip v c`.
* `c ∈ neg`: if `v = false`, the literal `¬v` satisfies it. If `v = true`, pick a `c₀ ∈ pos` with `strip v c₀` false. The resolvent `strip v c₀ ++ strip v c` lies in `eliminate v φ`, so it is true, and hence `strip v c` is true.

`eliminate_sat_iff` follows. `eliminate_no_v` shows that the variable really disappears: after `n` steps on `n` variables, the result is either `[]` (satisfiable) or contains the empty clause (unsatisfiable).

**Size law (`eliminate_length`).** This is direct: `|flatMap (c ↦ map (resolvent c) neg) pos| = Σ_{c∈pos} |neg| = |pos| · |neg|`.

**Blow-up family.** For `p, q ≥ 0`:

```
blowup p q = [x₀ ∨ x_{1+i} | i < p] ++ [¬x₀ ∨ x_{p+1+j} | j < q]
```

All side variables are distinct. `posClauses x₀` is the first block, `negClauses x₀` the second, and `restClauses x₀ = []`. So `eliminate_length` gives exactly `p · q` clauses, each of the form `x_{1+i} ∨ x_{p+1+j}` (`blowup_resolvent`). None of them is a tautology or a duplicate, so deleting duplicates or tautologies would not shrink the result.

**Worked numbers.** For `p = q = 50`, 100 clauses become 2,500. For `p = q = 1000`, 2,000 clauses become 1,000,000. A single step therefore grows the formula quadratically. Repeating steps can compound the growth, and Haken's theorem (below) shows that on the pigeonhole formulas *every* order generates exponentially many clauses in total.

**Why this refutes the route.** Every clause produced by `eliminate` is a resolvent of clauses already present. For an unsatisfiable `φ`, running elimination on all variables derives the empty clause. The list of all clauses produced during the run, in order, is then a resolution refutation of `φ` (a regular one, since each variable is resolved at most once on every path). Haken proved that every resolution refutation of the pigeonhole formula `PHP^{n+1}_n` has `2^{Ω(n)}` clauses. So for every elimination order, the total number of clauses generated on `PHP^{n+1}_n` is `2^{Ω(n)}`, while the input has only `O(n³)` clauses. This contradicts (Order). The informal step "the run is a resolution refutation" is standard. It is not formalized here; what is formalized is that each individual step is resolution on `v` plus deletion.

## 5. Known results and literature

* M. Davis and H. Putnam, "A computing procedure for quantification theory", *Journal of the ACM* 7(3), 1960. The elimination rule and its correctness.
* M. Davis, G. Logemann and D. Loveland, "A machine program for theorem-proving", *Communications of the ACM* 5(7), 1962. Replaces elimination by splitting (DPLL), precisely to avoid the memory blow-up.
* J. A. Robinson, "A machine-oriented logic based on the resolution principle", *Journal of the ACM* 12(1), 1965. General resolution.
* Z. Galil, "On the complexity of regular resolution and the Davis–Putnam procedure", *Theoretical Computer Science* 4, 1977. Exponential lower bounds for regular resolution, and hence for the Davis–Putnam procedure.
* A. Haken, "The intractability of resolution", *Theoretical Computer Science* 39, 1985. Resolution refutations of the pigeonhole principle need exponential size.
* A. Urquhart, "Hard examples for resolution", *Journal of the ACM* 34(1), 1987; V. Chvátal and E. Szemerédi, "Many hard examples for resolution", *Journal of the ACM* 35(4), 1988. Exponential lower bounds for Tseitin formulas on expanders and for random 3-CNF.
* R. Dechter and I. Rish, "Directional resolution: the Davis–Putnam procedure, revisited", KR 1994. Elimination along an order costs time and space exponential only in the induced width of that order.
* N. Eén and A. Biere, "Effective preprocessing in SAT through variable and clause elimination", SAT 2005. Modern solvers eliminate a variable only when the non-tautological resolvents are no more numerous than the clauses they replace, which is the "bounded variable elimination" heuristic.

None of these theorems are formalized here. The files formalize the single elimination step, its exactness, its size, and the multiplicative family.

## 6. How far the idea can be pushed toward P vs NP

At full potential, variable elimination is directional resolution. It is polynomial when the input has an elimination order of logarithmic induced width, which covers bounded-treewidth formulas (Idea 25 and Idea 26 give the same `2^{O(width)}` picture). In general, with duplicate clauses removed, it is bounded only by `2^{O(n)}`, since there are at most `3^n` distinct clauses on `n` variables. The `eliminate` of the files does not remove duplicates.

The would-be obligation (Order) is not open. It is false, since resolution has exponential lower bounds (Haken, Urquhart, Chvátal–Szemerédi). A stronger variant would add clause learning, subsumption, or extension variables to the elimination:

* Subsumption and deduplication keep the procedure inside resolution, so the same lower bounds apply.
* Adding *extension variables* changes the proof system to extended resolution (Idea 28), for which no superpolynomial lower bound is known.

So the only unblocked direction leaves this idea and becomes the open question of Idea 28 (see `ERSuperpolyLowerBound` there).

The open obligation, as stated in [Idea28.lean](../lean/Idea28.lean):

```lean
def ERSuperpolyLowerBound (family : Nat → CNF) : Prop :=
  (∀ n, ¬ Satisfiable (family n)) ∧
  ∀ c k : Nat, ∃ n, ∀ π, ERDerives (family n) π → [] ∈ π →
    c * (size (family n) + 1) ^ k < π.length
```

As an algorithmic route to P = NP, the idea is therefore closed. It gives no information about P ≠ NP: a lower bound for resolution is a lower bound for one proof system, and by Cook–Reckhow, NP ≠ coNP needs lower bounds for *every* propositional proof system.

## 7. Failure modes this idea catches

* **Hidden exponential work** (error family 2 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). Each step looks like "one variable fewer", but `eliminate_length` shows the clause count multiplies by `|neg|` for each positive clause. A claimed `n`-step polynomial algorithm must bound the *size*, not the number of steps.
* **Counting mistakes** (error family 7). "Each step removes a variable, so the formula shrinks" is false. `blowup_length` gives `p · q ≫ p + q`.
* **Ignoring known barriers** (error family 14). Any SAT algorithm whose trace on unsatisfiable inputs is a resolution refutation inherits Haken's `2^{Ω(n)}` lower bound. This covers elimination, DPLL, and CDCL with or without restarts, but not procedures that add extension variables.
* **Invalid transformations** (error family 4). Naive elimination variants that drop resolvents, or keep only "useful" ones, lose completeness. `eliminate_complete` shows exactly which clauses are needed: all `|pos| · |neg|` of them, apart from tautologies.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea27.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea27.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
