# Idea 18 — Structural restrictions and easy subclasses

**Verdict:** Refuted as a route (general theorem)

Special-case algorithms for restricted CNF classes are correct, and the files
prove this in general for three classes: 1-valid, 0-valid and unit CNF. For
unit CNF they also give a decision procedure that is proved correct. The route
"solve an easy subclass, therefore solve SAT" is refuted by a general theorem.
No satisfiability-preserving map of any kind, even an uncomputable one, sends
every CNF into a trivially satisfiable class. The only valid continuation
needs a polynomial-time reduction from SAT *into* the restricted class. In the
Lean file this is stated in the shared machine model: `ReducesInto L R` asks
for a `Complexity.Machine` that computes the map within a polynomial number of
`Run` steps (`Computes`). The open obligation `UnitReduction` (SAT reduces
into unit CNF by such a machine) gives `InP SAT` by
`inP_sat_of_unitReduction`, and `PEqualsNP` by `pEqualsNP_of_unitReduction`.
Both take as hypotheses the named known theorem `UnitSATInP` (a
polynomial-time machine decides unit CNF) and, for `PEqualsNP`, `SATHard`.
Neither is mechanised. The obligation is as hard as P = NP: if P = NP, the
reduction exists (decide, then output `[]` or `[[]]`). The size-only schema
`PolySizeReductionIntoFor` carries no P vs NP content, because
`unit_size_reduction_exists` proves it for unit CNF with a non-constructive
map. Schaefer's dichotomy (cited) tells which Boolean constraint classes are
NP-complete.

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
* The size-only schema `PolySizeReductionIntoFor R` says that such an `f`
  exists with `size (f φ) ≤ c*(size φ+1)^k`. It does not require `f` to be
  computable.
* Machine model (shared `Machines` layer). CNFs are encoded as words
  (`Machines.encodeCNF`, `Machines.decode`) and `ofM` reads a shared CNF in
  this file's syntax; `sat_ofM` says `Machines.SAT w = true ↔ Satisfiable (ofM
  (Machines.decode w))`.

  ```lean
  def ReducesInto (L : Language) (R : CNF → Prop) : Prop :=
    ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
      ∀ x, R (ofM (Machines.decode (f x))) ∧ L x = Machines.SAT (f x)

  def SATInPOn (R : CNF → Prop) : Prop :=
    ∃ (d : Machine) (p : Polynomial),
      Machines.DecidesOn d p (fun w => R (ofM (Machines.decode w))) Machines.SAT
  ```

  Time is the `Run` step count of the machine, and the output length is
  bounded by the running time (`Machines.computes_output_length`), so the
  polynomial size bound is part of `Computes`.
* **Open obligation** (Lean, `UnitReduction`):
  `def UnitReduction : Prop := ReducesInto Machines.SAT IsUnitCNF`.
* **Known theorem, not mechanised here** (`UnitSATInP`):
  `def UnitSATInP : Prop := SATInPOn IsUnitCNF`. The decider is the quadratic
  scan `unitDecide`, whose correctness is proved (`unitDecide_correct`); what
  is missing is a `Complexity.Machine` running it on encoded formulas. Unit
  CNF is a special case of Horn-SAT (Dowling–Gallier 1984) and of 2-SAT
  (Aspvall–Plass–Tarjan 1979).

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
| `PolySizeReductionIntoFor` (def) | Size-only schema: a satisfiability-preserving map into `R` with polynomial size blow-up. Computability is not part of the definition. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `poly_comp_bound` | `c'*(c*(n+1)^k+1)^k' ≤ (c'*(c+1)^k')*(n+1)^(k*k')` for all naturals. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `restriction_transfer` | Given the schema for `R`, a decider correct on `R` and a cost function `dcost` polynomially bounded in input size, the composite decides SAT correctly and `dcost` of the reduced instance is polynomially bounded in the original size. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |

| `sat_ofM` | The shared language `Machines.SAT` is satisfiability of the decoded CNF read in this file's syntax. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `ReducesInto` (def) | `L` reduces into the class `R` by a `Complexity.Machine` computing the map within a polynomial number of steps. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `SATInPOn` (def) | A polynomial-time machine decides SAT on every word that decodes into `R` (promise problem). | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `UnitSATInP` (def) | Known theorem, not mechanised: `SATInPOn IsUnitCNF`. Used only as a hypothesis. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `UnitReduction` (def) | Open obligation: `ReducesInto Machines.SAT IsUnitCNF`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `inP_of_reducesInto` | `ReducesInto L R` and `SATInPOn R` give `InP L` (via `Machines.inP_of_promise_reduction`). | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `reducesInto_preserves` | A machine reduction of SAT into `R` restricts to a satisfiability-preserving map of CNFs into `R`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `inP_sat_of_unitReduction` | `UnitSATInP → UnitReduction → InP Machines.SAT`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `pEqualsNP_of_unitReduction` | `SATHard → UnitSATInP → UnitReduction → PEqualsNP`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `pEqualsNP_of_reducesInto` | The same for every class `R` with `SATInPOn R`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `reducesInto_positive_const`, `not_reducesInto_positive` | A machine reduction into the 1-valid class forces a constant language, so SAT has none. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `exists_not_reducible` | Cantor over machines: for every `M` some language has no machine map `f` with `L x = M (f x)`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |
| `not_forall_reducesInto` | Non-vacuity: for every class `R`, `¬ ∀ L, ReducesInto L R`. | [Idea18.lean](../lean/Idea18.lean) | [Idea18.v](../rocq/Idea18.v) |

The cost function `dcost` in `restriction_transfer` is a hypothesis about the
schema only. The machine-model theorems take their costs from `Run` step
counts, so `inP_of_reducesInto` needs no separate cost argument. The machine
section is Lean only for now; the intended Rocq names are the same as the
Lean names.

The Lean file also proves `unit_size_reduction_exists`:
`PolySizeReductionIntoFor IsUnitCNF` holds, by sending satisfiable formulas to
`[]` and all others to `[[]]`. The map is defined by classical case analysis
and is not claimed to be efficient. This theorem is not in the Rocq file. Without
classical logic, a Rocq proof would need a verified satisfiability decision
procedure. It shows that the
size-only schema does not capture the open obligation, which is why the
obligation `UnitReduction` requires a machine that computes the map.

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
exactly these two conditions, with `O(|φ|)` and `O(|φ|²)` clause comparisons
(by inspection; the cost is not formalized).

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

**Transfer.** Let `f` witness `PolySizeReductionIntoFor R` with bound
`c*(n+1)^k`, and let `d` be correct on `R` with cost at most `c'*(m+1)^k'`
on inputs of size `m`. Then `d (f φ) = true ↔ Satisfiable (f φ) ↔
Satisfiable φ`. For the cost,
`size (f φ) + 1 ≤ c*(n+1)^k + 1 ≤ (c+1)*(n+1)^k`, so
`c'*(size(f φ)+1)^k' ≤ c'*(c+1)^k'*(n+1)^(k k')`. This is `poly_comp_bound`
combined with monotonicity of `x ↦ c'*(x+1)^k'`.

**Machine transfer.** Let `m` compute `f` within `p` steps with every `f x`
decoding into `R`, and let `d` decide SAT within `p'` steps on every word
decoding into `R`. Then `Machines.inP_of_promise_reduction` composes them into
a machine deciding `L` within a composed polynomial (`inP_of_reducesInto`).
The machine version of the trivial-class refutation is
`not_reducesInto_positive`: `SAT (encodeCNF [[]]) = false`, but a reduction
into the 1-valid class would make it `true`.

**Why the route is refuted.** A restricted class helps only when the
obligation `ReducesInto Machines.SAT R` holds. For trivial classes it provably
fails (by the previous theorems). For nontrivial classes in P, such as Horn,
2-CNF, unit CNF or affine, it gives `InP SAT` (`inP_of_reducesInto`), and with
`SATHard` (Cook–Levin hardness, not mechanised) it gives P = NP
(`pEqualsNP_of_reducesInto`). So proving it is at least as hard as proving
P = NP. For classes where it is known to hold, such as
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
* **Remaining obligation.** `UnitReduction := ReducesInto Machines.SAT
  IsUnitCNF`, or `ReducesInto Machines.SAT R` for any class `R` with
  `SATInPOn R`. The proved route is
  `pEqualsNP_of_unitReduction (hard : Machines.SATHard) (hU : UnitSATInP)
  (h : UnitReduction) : PEqualsNP`. Its two hypotheses besides the
  obligation are known theorems that are not mechanised: `SATHard`
  (Cook–Levin hardness, shared layer) and `UnitSATInP` (a machine running the
  quadratic unit-CNF scan). `not_forall_reducesInto` shows that the
  obligation is a statement about SAT: for every class `R` some language has
  no machine reduction into it. Conversely (argued, not mechanised), if
  P = NP then SAT reduces to any nontrivial class. Given an instance, decide
  it in polynomial time and output a fixed satisfiable or unsatisfiable
  member of `R`. So the obligation is *equivalent* to P = NP for every
  nontrivial `R ∈ P`, and false for trivial `R`. The machine requirement is
  essential. Without it the size-only schema already holds for unit CNF
  (`unit_size_reduction_exists`, Lean only).
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
  should demand a proof of `ReducesInto Machines.SAT R` for that class, with
  the reduction computed by a machine.
* **Family 4 (invalid reduction).** A "reduction" into a trivial class is
  refuted outright by `no_sat_reduction_into_positive`/`_negative` and
  `no_reduction_of_nontrivial`, whatever the construction.
* **Family 17 (encoding size).** `restriction_transfer` requires a size
  bound, and in the machine model it is implied by the running time
  (`Machines.computes_output_length`). A reduction into Horn or 2-CNF with exponential blow-up (for
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
