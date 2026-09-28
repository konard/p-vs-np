import proofs.experiments.issue532.lean.Idea36
open Issue532.Idea36

/-- Existence of a cost-minimal feasible solution (no `Nat.find` in core). -/
theorem exists_min {S : Type} (P : S → Prop) (c : S → Nat) (h : ∃ s, P s) :
    ∃ s, P s ∧ ∀ t, P t → c s ≤ c t := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ n, ∀ s, P s → c s < n → False := by
    intro n
    induction n with
    | zero => intro s _ hs; exact Nat.not_lt_zero _ hs
    | succ n ih =>
      intro s hs hlt
      apply hno
      refine ⟨s, hs, fun t ht => ?_⟩
      apply Classical.byContradiction
      intro hts
      exact ih t ht (by omega)
  obtain ⟨s, hs⟩ := h
  exact key (c s + 1) s hs (Nat.lt_succ_self _)

/-- (a) `lp` and `PolyTime` are free: whenever every instance is feasible, taking
`lp :=` the integral optimum and `rnd :=` a classical optimal solution meets
`ExactRoundingObligation (fun _ => True)`. -/
theorem idea36_exactRounding_trivial {Inst Sol : Type} (feasible : Inst → Sol → Prop)
    (cost : Inst → Sol → Nat) (hfeas : ∀ I, ∃ s, feasible I s) :
    ∃ lp, ExactRoundingObligation (fun _ => True) feasible cost lp := by
  have hmin := fun I => exists_min (feasible I) (cost I) (hfeas I)
  let rnd : Inst → Sol := fun I => Classical.choose (hmin I)
  have hr : ∀ I, feasible I (rnd I) ∧ ∀ t, feasible I t → cost I (rnd I) ≤ cost I t :=
    fun I => Classical.choose_spec (hmin I)
  refine ⟨fun I => cost I (rnd I), fun I s hs => (hr I).2 s hs, rnd, trivial,
    fun I => ⟨(hr I).1, Nat.le_refl _⟩⟩

/-- Instance: vertex cover itself (NP-hard) with the file's `IsCover`/`cost`. -/
theorem idea36_vertexCover_trivial :
    ∃ lp, ExactRoundingObligation (Inst := List Nat × List (Nat × Nat)) (Sol := Nat → Bool)
      (fun _ => True) (fun I C => IsCover I.2 C) (fun I C => cost I.1 C) lp :=
  idea36_exactRounding_trivial _ _ (fun _ => ⟨fun _ => true, fun _ _ => Or.inl rfl⟩)
