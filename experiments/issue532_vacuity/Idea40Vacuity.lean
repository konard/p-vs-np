import proofs.experiments.issue532.lean.Idea40
import proofs.experiments.issue532.lean.Idea25
open Issue532.Idea40

/-- (a) `baseCost`, `stepCost`, `base` and `step` are unconstrained functions
(no machine model): whenever every size `n` has instances of both answers, a
classical `step` (jump to an instance of size `n` with the same answer) with zero
cost meets `AdditiveSelfReduction`. For SAT with `size` = number of variables this
hypothesis holds, so the obligation is trivially true there. -/
theorem idea40_additive_trivial {Inst : Type} (size : Inst → Nat) (answer : Inst → Bool)
    (hrich : ∀ n b, ∃ J, size J = n ∧ answer J = b) :
    AdditiveSelfReduction size answer := by
  let step : Inst → Inst := fun I =>
    Classical.choose (hrich (size I - 1) (answer I))
  have hs : ∀ I, size (step I) = size I - 1 ∧ answer (step I) = answer I :=
    fun I => Classical.choose_spec (hrich (size I - 1) (answer I))
  refine ⟨answer, step, fun _ => 0, fun _ => 0, 0, 0, 0,
    fun _ _ => rfl, fun _ => Nat.le_refl _, ?_, fun _ => Nat.zero_le _⟩
  intro I n hI
  obtain ⟨h1, h2⟩ := hs I
  exact ⟨by rw [h1, hI]; rfl, h2⟩

/-- Concrete instance: instances are (claimed-size, bit) pairs. Any language whose
instances of each size realise both answers behaves the same way. -/
example : AdditiveSelfReduction (Inst := Nat × Bool) Prod.fst Prod.snd :=
  idea40_additive_trivial _ _ (fun n b => ⟨(n, b), rfl, rfl⟩)

/-! ## Instance: real CNF-SAT (CNF syntax from Idea 25), size = number of literal occurrences -/

section SATInstance
open Issue532.Idea25 (CNF Satisfiable vars clauseVars evalCNF evalClause evalLit Lit)
attribute [local instance] Classical.propDecidable

noncomputable def satAnswer (φ : CNF) : Bool := decide (Satisfiable φ)

def posUnits (n : Nat) : CNF := List.replicate n [⟨0, true⟩]

theorem vars_posUnits (n : Nat) : (vars (posUnits n)).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [posUnits, List.replicate_succ, vars, clauseVars] at *; omega

theorem posUnits_sat (n : Nat) : Satisfiable (posUnits n) := by
  refine ⟨fun _ => true, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => simpa [posUnits, List.replicate_succ, evalCNF, evalClause, evalLit] using ih

theorem emptyClause_unsat (n : Nat) : ¬ Satisfiable ([] :: posUnits n) := by
  rintro ⟨a, ha⟩
  simp [evalCNF, evalClause] at ha

theorem idea40_additive_SAT :
    AdditiveSelfReduction (fun φ : CNF => (vars φ).length) satAnswer := by
  apply idea40_additive_trivial
  intro n b
  cases b
  · refine ⟨[] :: posUnits n, ?_, ?_⟩
    · simp [vars, clauseVars, vars_posUnits]
    · simp [satAnswer, emptyClause_unsat n]
  · exact ⟨posUnits n, vars_posUnits n, by simp [satAnswer, posUnits_sat n]⟩

end SATInstance
