import proofs.experiments.issue532.lean.Idea26
open Issue532.Idea26
attribute [local instance] Classical.propDecidable

theorem unsat_emptyClause : ¬ Satisfiable [[]] := by
  rintro ⟨a, ha⟩
  simp [evalCNF, evalClause] at ha

/-- Classical map: `([], [], [])` for satisfiable inputs, `([[]], [], [])` otherwise. -/
noncomputable def oracleSep (φ : CNF) : CNF × CNF × List Nat :=
  if Satisfiable φ then ([], [], []) else ([[]], [], [])

/-- (a) With the free class `PolyTime := fun _ => True`, `SeparatorObligation`
holds with an empty separator (`w = 0`). -/
theorem idea26_separatorObligation_trivial :
    SeparatorObligation (fun _ => True) (fun _ => 0) := by
  refine ⟨oracleSep, trivial, fun φ => ?_⟩
  by_cases h : Satisfiable φ
  · rw [show oracleSep φ = ([], [], []) by simp [oracleSep, h]]
    refine ⟨fun v hv => by simp [vars] at hv, Nat.le_refl _, ?_⟩
    exact ⟨fun _ => ⟨fun _ => true, rfl⟩, fun _ => h⟩
  · rw [show oracleSep φ = ([[]], [], []) by simp [oracleSep, h]]
    refine ⟨fun v hv => by simp [vars, clauseVars] at hv, Nat.le_refl _, ?_⟩
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (by simpa using unsat_emptyClause)⟩
