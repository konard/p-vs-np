import proofs.experiments.issue532.lean.Idea25
open Issue532.Idea25
attribute [local instance] Classical.propDecidable

/-- The empty clause is unsatisfiable. -/
theorem unsat_emptyClause : ¬ Satisfiable [[]] := by
  rintro ⟨a, ha⟩
  simp [evalCNF, evalClause] at ha

/-- Classical "oracle" map: `[]` for satisfiable inputs, `[[[]]]` (one component
consisting of the empty clause) otherwise. -/
noncomputable def oracleSplit (φ : CNF) : List CNF :=
  if Satisfiable φ then [] else [[[]]]

theorem oracleSplit_spec (φ : CNF) : DisjointChain (oracleSplit φ) ∧
    (∀ ψ, ψ ∈ oracleSplit φ → (vars ψ).length ≤ 0) ∧
    (Satisfiable φ ↔ Satisfiable (joinAll (oracleSplit φ))) := by
  by_cases h : Satisfiable φ
  · rw [show oracleSplit φ = [] by simp [oracleSplit, h]]
    refine ⟨trivial, fun ψ hψ => by simp at hψ, ?_⟩
    exact ⟨fun _ => ⟨fun _ => true, rfl⟩, fun _ => h⟩
  · rw [show oracleSplit φ = [[[]]] by simp [oracleSplit, h]]
    refine ⟨⟨fun v hv => by simp [vars, clauseVars] at hv, trivial⟩, ?_, ?_⟩
    · intro ψ hψ
      simp at hψ; subst hψ; simp [vars, clauseVars]
    · exact ⟨fun h' => absurd h' h, fun h' => absurd h' (by simpa [joinAll] using unsat_emptyClause)⟩

/-- (a) Any `PolyTime` class admitting the classical oracle map (in particular the
free class `fun _ => True`) makes `ComponentObligation` true for every width
bound `w`, including `w = 0`. -/
theorem idea25_componentObligation_of (PolyTime : (CNF → List CNF) → Prop)
    (hP : PolyTime oracleSplit) (w : Nat → Nat) : ComponentObligation PolyTime w := by
  refine ⟨oracleSplit, hP, fun φ => ?_⟩
  obtain ⟨hd, hw, hp⟩ := oracleSplit_spec φ
  exact ⟨hd, fun ψ hψ => Nat.le_trans (hw ψ hψ) (Nat.zero_le _), hp⟩

theorem idea25_componentObligation_trivial :
    ComponentObligation (fun _ => True) (fun _ => 0) :=
  idea25_componentObligation_of _ trivial _
