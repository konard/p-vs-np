import proofs.experiments.issue532.lean.Idea16
open Issue532.Idea16

/-- (a) The technique `T` is a free parameter.  Adjoining to `{S}` the
world-dependent statement `(· = real)` makes `T` non-relativizing for free, so
`∃ T, NonRelativizingIngredient T real S` is *equivalent to `S real`*: the
"non-relativizing ingredient" contributes nothing beyond the target itself. -/
theorem idea16_ingredient_iff (real : World) (S : World → Prop) :
    (∃ T, NonRelativizingIngredient T real S) ↔ S real := by
  constructor
  · rintro ⟨T, hsound, hT, _⟩
    exact hsound S hT
  · intro hreal
    refine ⟨fun S' => S' = S ∨ S' = (· = real), ?_, Or.inl rfl, ?_⟩
    · rintro S' (rfl | rfl)
      · exact hreal
      · rfl
    · intro hR
      have h := hR (· = real) (Or.inr rfl) (fun n => !real n)
      have := congrFun h 0
      cases hr : real 0 <;> simp [hr] at this

/-- A concrete instance, provable in one line. -/
theorem idea16_concrete :
    ∃ T, NonRelativizingIngredient T (fun _ => false) (fun O => O 0 = false) :=
  (idea16_ingredient_iff _ _).2 rfl
