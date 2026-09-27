# Idea 18 — Structural restrictions and easy subclasses

**Verdict:** Refuted as a route (general theorem)

Special-case algorithms for restricted CNF classes are correct, and the files
prove this in general for three classes: 1-valid, 0-valid and unit CNF. For
unit CNF they also give a verified quadratic decision procedure. The route
"solve an easy subclass, therefore solve SAT" is refuted by a general theorem.
No satisfiability-preserving map of any kind, even an uncomputable one, sends
every CNF into a trivially satisfiable class. The only valid continuation
needs a size-bounded reduction from SAT *into* the restricted class
(`PolySizeReductionInto`). The composition theorem is proved conditionally. By
Schaefer's dichotomy, this obligation can hold only for classes that are
themselves NP-complete, or else it implies P = NP.

## 1. The idea at full strength

Part I item 1 of issue #532 says: "Restricting geometry, connectivity, or
structure collapses hardness. Hardness arises from **combinatorial freedom**".
Phase 6 lists "restricted SAT variants" as training grounds. At full strength
the idea claims:

> Find a structural restriction under which SAT is polynomial, and show that
> every instance can be brought into that form. Then P = NP.

The first half is often achievable (Horn, 2-CNF, unit, 1-valid, 0-valid,
affine). The second half is the whole problem.

## 2. Precise mathematical formulation

* Literals are `⟨var, pos⟩ : Nat × Bool`, clauses are lists of literals, a
  CNF is a list of clauses, and an assignment is `Nat → Bool`. `evalLit`,
  `evalClause` (a disjunction; empty clause = false) and `evalCNF` (a
  conjunction; empty CNF = true) are defined by recursion.
  `Satisfiable φ := ∃ a, evalCNF a φ = true`.
* `size φ` is the sum over clauses of `(length C + 1)`.
* Classes:
  * `PositiveClauses φ`: every clause has a positive literal (1-valid).
  * `NegativeClauses φ`: every clause has a negative literal (0-valid).
  * `IsUnitCNF φ`: every clause has length at most 1.
* A reduction of SAT into a class `R` is a map `f : CNF → CNF` with
  `R (f φ)` and `Satisfiable φ ↔ Satisfiable (f φ)` for all `φ`.
* The required claim for the full-strength idea is
  `PolySizeReductionInto R`: such an `f` exists with
  `size (f φ) ≤ c*(size φ+1)^k`. The idea also needs `f` to be computable in
  polynomial time, which cannot be stated without a machine model and is
  recorded in prose. On top of this, `R` must have a polynomial-time decider.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `evalClause_true_iff`, `evalCNF_true_iff` | A clause is true iff some literal is true; a CNF is true iff every clause is true. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `allTrue_satisfies` | Every CNF with a positive literal in each clause is satisfied by the all-true assignment. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `allFalse_satisfies` | Every CNF with a negative literal in each clause is satisfied by the all-false assignment. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `positive_satisfiable`, `negative_satisfiable` | Those CNFs are satisfiable. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `clause_of_length_le_one` | A nonempty clause of length at most 1 is a singleton. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `unitCNF_sat_iff` | For every unit CNF: satisfiable iff no empty clause and no pair `[x]`, `[¬x]`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `unitDecide_correct` | The Boolean procedure `unitDecide` (one emptiness scan plus a pairwise scan) returns `true` iff the unit CNF is satisfiable. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `reduction_into_trivial_class` | If `L x ↔ M (f x)` for all `x` and `M` is identically true, then `L` is identically true. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `no_reduction_of_nontrivial` | A predicate with a no-instance has no reduction (by any function) to an identically true predicate. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `empty_clause_unsat` | `[[]]` is unsatisfiable. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `no_sat_reduction_into_positive` / `no_sat_reduction_into_negative` | No function `CNF → CNF` both preserves satisfiability and lands in the 1-valid (resp. 0-valid) class. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `PolySizeReductionInto` (def) | Open obligation: a satisfiability-preserving map into `R` with polynomial size blow-up. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `poly_comp_bound` | `c'*(c*(n+1)^k+1)^k' ≤ (c'*(c+1)^k')*(n+1)^(k*k')` for all naturals. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `restriction_transfer` | Given the obligation for `R`, a decider correct on `R` and polynomially cost-bounded in input size, the composite decides SAT correctly with polynomially bounded decider cost in the original size. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |

The Rocq `unitDecide` tests for the empty clause with `existsb isEmptyClause`,
while the Lean version uses `decide ([] ∈ φ)`. The two are extensionally the
same test, and both are proved correct.

## 4. Complete argument

**1-valid and 0-valid.** If every clause contains a positive literal `l`,
then under the all-true assignment `evalLit a l = a l.var = true`, so every
clause and hence the CNF is true. The 0-valid case is dual. These classes are
*trivial*: the decision problem has constant answer `true`.

**Unit CNF.** (⇒) A satisfying `a` makes every clause true. The empty clause
is false, so it is absent. If `[l₁]` and `[l₂]` share a variable with
opposite signs, then `evalLit a l₁` and `evalLit a l₂` are `a v` and `¬ a v`
in some order, and they cannot both be true. (⇐) Define
`a v := ([⟨v,true⟩] ∈ φ)`. Each clause is a nonempty clause of length at most
1, so it is `[l]`. If `l` is positive, then `[⟨l.var,true⟩] = [l] ∈ φ`, so
`a l.var = true`. If `l` is negative and `a l.var = true`, then
`[⟨l.var,true⟩] ∈ φ` together with `[l] ∈ φ` is a clash, which contradicts
the hypothesis. Hence `a l.var = false` and `¬x` holds. `unitDecide` checks
exactly these two conditions, with `O(|φ|)` and `O(|φ|²)` clause comparisons.

*Worked example.* `φ = [[x₁], [¬x₂], [x₃], [¬x₁]]` has the clash
`[x₁], [¬x₁]` and is unsatisfiable. Removing `[¬x₁]` gives the model
`x₁ = x₃ = true`, `x₂ = false`, which is exactly the constructed `a`.

**Trivial classes admit no reductions.** Suppose `f` preserves
satisfiability and always lands in the 1-valid class. Then
`f [[]]` is satisfiable (1-valid), so `[[]]` is satisfiable, which is false.
The proof uses no property of `f` beyond these two, so it rules out every
function, including non-computable ones and functions of any size. The
abstract lemma `no_reduction_of_nontrivial` is the same argument for arbitrary
predicates.

**Transfer.** Let `f` witness `PolySizeReductionInto R` with bound
`c*(n+1)^k`, and let `d` be correct on `R` with cost at most `c'*(m+1)^k'`
on inputs of size `m`. Then `d (f φ) = true ↔ Satisfiable (f φ) ↔
Satisfiable φ`. For the cost,
`size (f φ) + 1 ≤ c*(n+1)^k + 1 ≤ (c+1)*(n+1)^k`, so
`c'*(size(f φ)+1)^k' ≤ c'*(c+1)^k'*(n+1)^(k k')`. This is `poly_comp_bound`
combined with monotonicity of `x ↦ c'*(x+1)^k'`.

**Why the route is refuted.** A restricted class helps only when the
obligation holds. For trivial classes it provably fails (by the previous
theorem). For nontrivial classes in P, such as Horn, 2-CNF, unit CNF or
affine, it combines with `restriction_transfer` to give a polynomial SAT
algorithm (after adding the cost of computing `f`). So proving it is at least
as hard as proving P = NP. For classes where it is known to hold, such as
3-CNF, 1-in-3-SAT or NAE-3-SAT, the class is NP-complete, and the
restriction is not "easy". The special-case algorithm therefore never
transfers unless P = NP is proved by other means.

## 5. Known results and literature

* T. J. Schaefer, "The complexity of satisfiability problems", *STOC* 1978.
  Dichotomy for Boolean constraint languages. SAT(Γ) is in P when Γ is
  0-valid, 1-valid, Horn, dual-Horn, bijunctive (2-CNF) or affine, and
  NP-complete otherwise.
* B. Aspvall, M. F. Plass, R. E. Tarjan, "A linear-time algorithm for testing
  the truth of certain quantified Boolean formulas", *Information Processing
  Letters* 8(3) (1979). 2-SAT in linear time via strongly connected
  components.
* W. F. Dowling and J. H. Gallier, "Linear-time algorithms for testing the
  satisfiability of propositional Horn formulae", *Journal of Logic
  Programming* 1(3) (1984). Horn-SAT in linear time. Idea 24 formalizes a
  unit-propagation decision procedure for Horn.
* S. A. Cook, "The complexity of theorem-proving procedures", *STOC* 1971.
  SAT, and 3-SAT, are NP-complete.
* A. A. Bulatov, "A dichotomy theorem for nonuniform CSPs", *FOCS* 2017,
  and D. Zhuk, "A proof of the CSP dichotomy conjecture", *FOCS* 2017.
  These extend the dichotomy to all finite domains.

None of these results is formalized here. The formal content is limited to
the 1-valid, 0-valid and unit classes and to the abstract reduction and
transfer theorems.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** Restrictions give correct polynomial algorithms on
  their classes. Combined with a reduction, they give *exactly*
  `restriction_transfer`: correctness of the composite and a composed
  polynomial cost.
* **Remaining obligation.** `PolySizeReductionInto R` for a class `R` with a
  polynomial-time decider, plus polynomial-time computability of the
  reduction. For any such `R` this obligation implies P = NP. Conversely, if
  P = NP then SAT reduces to any nontrivial class. Given an instance, decide
  it in polynomial time and output a fixed satisfiable or unsatisfiable
  member of `R`. So the obligation is *equivalent* to P = NP for every
  nontrivial `R ∈ P`, and false for trivial `R`.
* **Barriers.** Schaefer's theorem already classifies which Boolean
  restrictions stay hard. Unless P = NP, no Boolean constraint language
  outside the six tractable cases is in P, and none inside them admits the
  reduction. Any new restriction must either fall into Schaefer's framework
  (so its status is known) or be a non-CSP restriction (for example
  structural width parameters, see Idea 37). Bounded treewidth and similar
  parameters are polynomial only when the parameter is bounded, and a
  hardness-preserving reduction would have to increase the parameter
  unboundedly.

## 7. Failure modes this idea catches

* **Family 5 (special or different problem).** An algorithm that works on a
  structurally restricted class is a special-case algorithm. The auditor
  should demand a proof of `PolySizeReductionInto` for that class.
* **Family 4 (invalid reduction).** A "reduction" into a trivial class is
  refuted outright by `no_sat_reduction_into_positive`/`_negative` and
  `no_reduction_of_nontrivial`, whatever the construction.
* **Family 17 (encoding size).** `restriction_transfer` requires a size
  bound. A reduction into Horn or 2-CNF with exponential blow-up (for
  example, expanding to a truth table) does not give a polynomial algorithm.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea18.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea18.v
rm -f proofs/experiments/issue532/rocq/Idea18.vo proofs/experiments/issue532/rocq/Idea18.vok \
      proofs/experiments/issue532/rocq/Idea18.vos proofs/experiments/issue532/rocq/Idea18.glob \
      proofs/experiments/issue532/rocq/.Idea18.aux
```

Both commands print nothing on success.
