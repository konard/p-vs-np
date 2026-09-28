import proofs.experiments.issue532.lean.Idea12
open Issue532.Idea12

/-- (a) `PolyDecider` holds for every language: `Algo.time` is a free field. -/
theorem idea12_polyDecider_trivial {α : Type} (sz : α → Nat) (L : α → Bool) :
    PolyDecider sz L :=
  ⟨⟨L, fun _ => 0⟩, fun _ => rfl, 0, 0, fun _ => Nat.zero_le _⟩

/-- (b) the lower-bound hypothesis `¬ PolyDecider` of `hardness_transfer` is refutable. -/
theorem idea12_not_not_polyDecider {α : Type} (sz : α → Nat) (L : α → Bool) :
    ¬ ¬ PolyDecider sz L :=
  fun h => h (idea12_polyDecider_trivial sz L)

/-- (a) Every `L` has a `PolyReduction` (time 0, output of constant size) to every
nontrivial `M`, via the constant-choice map of `reduces_to_any_nontrivial`. -/
theorem idea12_polyReduction_trivial {α β : Type} (szA : α → Nat) (szB : β → Nat)
    (L : α → Bool) (M : β → Bool) (hM : Nontrivial M) :
    ∃ R : Algo α β, PolyReduction szA szB L M R := by
  obtain ⟨a, b, ha, hb⟩ := hM
  refine ⟨⟨fun x => if L x then a else b, fun _ => 0⟩, ?_, szB a + szB b, 0, fun x => ⟨?_, ?_⟩⟩
  · intro x; cases h : L x <;> simp [h, ha, hb]
  · exact Nat.zero_le _
  · show szB (if L x = true then a else b) ≤ (szB a + szB b) * (szA x + 1) ^ 0
    cases L x <;> simp <;> omega
