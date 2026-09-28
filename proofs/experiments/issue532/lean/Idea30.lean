import proofs.experiments.issue532.lean.Circuits
import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue #532, Idea 30: unrestricted circuit lower bounds (transfer and counting)

**Verdict: developed to an open obligation (conditional theorem proved).**

Everything is stated over the shared layer: the machine model of
`Complexity`/`Machines` (`InP`, `InNP`, `SAT`) and the shared NAND circuit
model of `Circuits` (`Circuit`, `wires`, `output`, `WF`, `InPPoly`,
`SuperpolyLowerBound`).

* *Transfer* (`lower_bound_transfer`, `no_fast_algorithm`): a circuit lower
  bound, a simulation of fast algorithms by small circuits, and a size bound
  together exclude a fast algorithm. For the machine model the simulation is
  the known theorem `PSubsetPPoly` (P ⊆ P/poly), used only as a named
  hypothesis.
* *Shannon counting*: the counting core (`words`, `allBool`, `fnOfTable`,
  `uncovered_table`, `shannon_codes`, `shannon_circuits`) now lives in
  `Circuits.lean` over the shared circuit model; this file keeps the concrete
  instance `four_bit_function_needs_three_gates`. `Circuits.exists_not_inPPoly`
  uses counting to show that a language outside P/poly exists.

Counting is non-explicit: it never names the hard function, and its hard
language is not known to be in NP. The open obligations are
`SATCircuitLowerBound` (SAT needs superpolynomial circuits) and
`ExplicitNPLowerBound` (some NP language does). With `PSubsetPPoly` (and
`SATInNP` for the SAT version) each gives `PNotEqualsNP`
(`sat_lower_bound_separates`, `explicit_lower_bound_separates`). `SATInNP` is
proved in `SATVerifier.lean` (`SATVerifier.satInNP`), so `explicit_of_sat'` and
`sat_lower_bound_separates'` drop that premise; `PSubsetPPoly` remains a named
hypothesis. Nothing here proves such a bound. Natural proofs, relativization and algebrization constrain
how it could be proved.
-/

namespace Issue532.Idea30

open Complexity Issue532.Machines Issue532.Circuits

/-- The abstract conditional contradiction. -/
theorem lower_bound_transfer {Algorithm Circuit : Type}
    (compile : Algorithm → Circuit) (fast : Algorithm → Prop)
    (correct expensive : Circuit → Prop)
    (lowerBound : ∀ c, correct c → expensive c)
    (simulation : ∀ a, fast a → correct (compile a))
    (sizeBound : ∀ a, fast a → ¬ expensive (compile a)) :
    ∀ a, ¬ fast a :=
  fun a ha => (sizeBound a ha) (lowerBound (compile a) (simulation a ha))

/-! ## Shannon counting: a concrete instance

The general counting theorems (`words_length`, `mem_words`, `words_nodup`,
`allBool_length`, `tables_length`, `table_of_fnOfTable`, `cover_length`,
`uncovered_table`, `codesUpTo_length`, `shannon_codes`, `shannon_circuits`)
are in `Circuits.lean`, stated over the shared `wires`/`output`/`WF`. -/

/-- Concrete instance: some Boolean function on 4 bits needs more than 2 NAND gates. -/
theorem four_bit_function_needs_three_gates :
    ∃ f : Language, ∀ C, WF 4 C → C.length ≤ 2 →
      ∃ x, x.length = 4 ∧ output x C ≠ f x :=
  shannon_circuits 4 2 (by decide)

/-! ## Transfer over the shared model -/

/-- A superpolynomial lower bound excludes polynomial-size circuits. -/
theorem superpoly_excludes_poly_circuits (f : Language)
    (h : SuperpolyLowerBound f) : ¬ InPPoly f :=
  (superpoly_iff_not_inPPoly f).mp h

/-- Transfer to algorithms, given the simulation of fast algorithms by
polynomial-size circuits as a hypothesis (a schema over an abstract algorithm
type). -/
theorem no_fast_algorithm {Algorithm : Type} (computes : Algorithm → Language)
    (fast : Algorithm → Prop)
    (simulation : ∀ a, fast a → InPPoly (computes a))
    (f : Language) (h : SuperpolyLowerBound f) :
    ∀ a, fast a → computes a ≠ f := by
  intro a ha e
  apply superpoly_excludes_poly_circuits f h
  rw [← e]
  exact simulation a ha

/-- For the machine model: under `PSubsetPPoly`, a language with a
superpolynomial circuit lower bound is not in P. -/
theorem not_inP_of_superpoly (hP : PSubsetPPoly) (f : Language)
    (h : SuperpolyLowerBound f) : ¬ InP f :=
  not_inP_of_not_inPPoly hP (superpoly_excludes_poly_circuits f h)

/-! ## The open obligations -/

/-- **Open obligation.** SAT (`Issue532.Machines.SAT`) has a superpolynomial
lower bound for the shared NAND circuit model. Not known; equivalent to
`¬ InPPoly SAT` (`superpoly_iff_not_inPPoly`). -/
def SATCircuitLowerBound : Prop := SuperpolyLowerBound SAT

/-- **Open obligation.** Some language in NP (the shared `InNP`) has a
superpolynomial circuit lower bound, i.e. NP ⊄ P/poly. -/
def ExplicitNPLowerBound : Prop := ∃ L : Language, InNP L ∧ SuperpolyLowerBound L

/-- Schema (the pre-refactor form): an explicit function in a class `NPClass`
with a superpolynomial circuit lower bound. It is only as strong as the class
supplied; `ExplicitNPLowerBound` is its instance at `InNP`. -/
def ExplicitNPLowerBoundFor (NPClass : Language → Prop) : Prop :=
  ∃ f, NPClass f ∧ SuperpolyLowerBound f

theorem explicitNPLowerBound_iff_for : ExplicitNPLowerBound ↔ ExplicitNPLowerBoundFor InNP :=
  Iff.rfl

/-- The SAT obligation implies the NP obligation (given `SATInNP`). -/
theorem explicit_of_sat (mem : SATInNP) (h : SATCircuitLowerBound) : ExplicitNPLowerBound :=
  ⟨SAT, mem, h⟩

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem explicit_of_sat' (h : SATCircuitLowerBound) : ExplicitNPLowerBound :=
  explicit_of_sat SATVerifier.satInNP h

/-- **Conditional theorem (SAT form).** Given the membership half of
Cook–Levin and the known theorem P ⊆ P/poly as named hypotheses, a
superpolynomial circuit lower bound for SAT gives P ≠ NP. -/
theorem sat_lower_bound_separates (mem : SATInNP) (hP : PSubsetPPoly)
    (h : SATCircuitLowerBound) : PNotEqualsNP :=
  pNotEqualsNP_of_superpoly_sat mem hP h

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped.
`PSubsetPPoly` remains a named hypothesis. -/
theorem sat_lower_bound_separates' (hP : PSubsetPPoly) (h : SATCircuitLowerBound) :
    PNotEqualsNP :=
  sat_lower_bound_separates SATVerifier.satInNP hP h

/-- **Conditional theorem.** Given P ⊆ P/poly as a named hypothesis, an NP
language with a superpolynomial circuit lower bound gives P ≠ NP. -/
theorem explicit_lower_bound_separates (hP : PSubsetPPoly)
    (h : ExplicitNPLowerBound) : PNotEqualsNP := by
  obtain ⟨L, hL, hlb⟩ := h
  exact pNotEqualsNP_of_superpoly hP hL hlb

/-- The weaker, unconditional-on-`PSubsetPPoly` reading: the obligation
exhibits an NP language outside P/poly. -/
theorem explicit_lower_bound_not_inPPoly (h : ExplicitNPLowerBound) :
    ∃ L, InNP L ∧ ¬ InPPoly L := by
  obtain ⟨L, hL, hlb⟩ := h
  exact ⟨L, hL, superpoly_excludes_poly_circuits L hlb⟩

/-- Schema version of the pre-refactor conditional: the obligation for a class
`NPClass` plus a simulation hypothesis yields a function in `NPClass` computed
by no fast algorithm. -/
theorem explicit_lower_bound_separatesFor {Algorithm : Type}
    (NPClass : Language → Prop) (computes : Algorithm → Language)
    (fast : Algorithm → Prop)
    (simulation : ∀ a, fast a → InPPoly (computes a))
    (h : ExplicitNPLowerBoundFor NPClass) :
    ∃ f, NPClass f ∧ ∀ a, fast a → computes a ≠ f := by
  obtain ⟨f, hf, hlb⟩ := h
  exact ⟨f, hf, no_fast_algorithm computes fast simulation f hlb⟩

/-! ## Non-vacuity -/

/-- The constant-`false` language is decided in one step by the empty machine. -/
theorem inP_const_false : InP (fun _ => false) :=
  inP_of_decidesWithin (m := ⟨[]⟩) (p := ⟨1, 0⟩)
    (fun _ => ⟨1, false, by simp [Polynomial.eval], Run.halt rfl, rfl⟩)

/-- The NP half of `ExplicitNPLowerBound` is satisfiable. -/
theorem inNP_const_false : InNP (fun _ => false) := pSubsetNP _ inP_const_false

/-- The lower-bound half is satisfiable: counting gives a (non-explicit)
language with a superpolynomial circuit lower bound. -/
theorem lower_bound_half_satisfiable : ∃ L : Language, SuperpolyLowerBound L :=
  exists_superpolyLowerBound

/-- The lower-bound half is not trivially true: constant languages have
two- and three-gate circuits, so they have no superpolynomial lower bound. -/
theorem const_no_lower_bound (b : Bool) : ¬ SuperpolyLowerBound (fun _ => b) :=
  fun h => (superpoly_iff_not_inPPoly _).mp h (inPPoly_const b)

/-- Counting alone proves the schema for the trivial class: the gap to the
obligation is exactly NP membership of a hard function (explicitness). -/
theorem counting_gives_schema_for_all_languages : ExplicitNPLowerBoundFor (fun _ => True) := by
  obtain ⟨L, hL⟩ := exists_superpolyLowerBound
  exact ⟨L, trivial, hL⟩

end Issue532.Idea30
