import proofs.experiments.issue532.lean.Idea32
open Issue532.Idea32
attribute [local instance] Classical.propDecidable

/-- The classical (non-computable) SAT "decider". -/
noncomputable def classicalSat (φ : CNF) : Bool := decide (Satisfiable φ)

theorem classicalSat_correct (φ : CNF) : classicalSat φ = true ↔ Satisfiable φ := by
  simp [classicalSat]

/-- (a) Any `PolyTime` class admitting `isolate classicalSat` (in particular the
free class `fun _ => True`) satisfies `IsolationObligation`. -/
theorem idea32_isolation_of (PolyTime : (CNF → CNF) → Prop)
    (hP : PolyTime (isolate classicalSat)) : IsolationObligation PolyTime :=
  let h := decider_meets_isolation classicalSat classicalSat_correct
  ⟨isolate classicalSat, hP, h.1, h.2⟩

theorem idea32_isolation_trivial : IsolationObligation (fun _ => True) :=
  idea32_isolation_of _ trivial

/-- (b) and with the empty class it is refutable. -/
theorem idea32_not_isolation_empty : ¬ IsolationObligation (fun _ => False) :=
  fun ⟨_, hf, _⟩ => hf
