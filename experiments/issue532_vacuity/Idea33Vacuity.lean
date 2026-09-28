import proofs.experiments.issue532.lean.Idea33
open Issue532.Idea33

/-- (a) With the free class `Efficient := fun _ => True`, the obligation holds for
every `L` and every error budget (take `B := L`). -/
theorem idea33_obligation_trivial (L : List Bool → Bool) (δ : Nat → Nat) :
    WorstToAverageObligation (fun _ => True) L δ :=
  fun _ => ⟨L, trivial, fun _ => rfl⟩

/-- (a) Any class containing `L` itself works. -/
theorem idea33_obligation_of_mem (Efficient : (List Bool → Bool) → Prop)
    (L : List Bool → Bool) (hL : Efficient L) (δ : Nat → Nat) :
    WorstToAverageObligation Efficient L δ :=
  fun _ => ⟨L, hL, fun _ => rfl⟩

/-- (a) The empty class makes it vacuously true as well. -/
theorem idea33_obligation_empty (L : List Bool → Bool) (δ : Nat → Nat) :
    WorstToAverageObligation (fun _ => False) L δ :=
  fun ⟨_, h, _⟩ => h.elim

/-- (b) The negation is trivially realised too (already `obligation_not_automatic`). -/
theorem idea33_not_obligation (L : List Bool → Bool) :
    ∃ Efficient, ¬ WorstToAverageObligation Efficient L (fun _ => 1) :=
  obligation_not_automatic L
