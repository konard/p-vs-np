import proofs.experiments.issue532.lean.Idea22
open Issue532.Idea22

/-- (a) `ExactPolyDecider` is trivial in the zero cost model (already in the file as
`zero_cost_trivial`), hence so is `PolySearch`. -/
theorem idea22_exactPolyDecider_trivial : ExactPolyDecider (fun _ _ => 0) := zero_cost_trivial

theorem idea22_polySearch_trivial : PolySearch (fun _ _ => 0) :=
  decision_to_search _ zero_cost_trivial

/-- Any cost model that charges nothing to `satDec` works. -/
theorem idea22_exactPolyDecider_of_free (Cost : CostModel) (h : ∀ ψ, Cost satDec ψ = 0) :
    ExactPolyDecider Cost :=
  ⟨satDec, 0, 0, satDec_correct, fun ψ => by simp [h ψ]⟩
