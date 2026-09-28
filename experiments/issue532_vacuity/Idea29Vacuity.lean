import proofs.experiments.issue532.lean.Idea29
open Issue532.Idea29
attribute [local instance] Classical.propDecidable

/-- (a) The `time` field of `PolyDecider` is free, so every language is in `InP`
(classical decision, time 0, bound `0 * (n+1)^0`). -/
noncomputable def freeDecider {α : Type} (sa : α → Nat) (L : α → Prop) : PolyDecider sa L where
  decide := fun x => decide (L x)
  time := fun _ => 0
  bound := ⟨0, 0⟩
  correct := fun x => by simp
  time_le := fun _ => Nat.zero_le _

theorem idea29_inP_trivial {α : Type} (sa : α → Nat) (L : α → Prop) : InP sa L :=
  ⟨freeDecider sa L⟩

/-- (a) Hence the open obligation `ReducesToP` holds for every language, e.g. SAT. -/
theorem idea29_reducesToP_trivial {α : Type} (sa : α → Nat) (L : α → Prop) :
    ReducesToP sa L :=
  (reducesToP_iff_inP sa L).mpr (idea29_inP_trivial sa L)
