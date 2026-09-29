import proofs.experiments.issue532.lean.Idea38
open Issue532.Idea38

/-- (a) `Proves` is a free predicate: the "prove everything" method trivially has a
nonrelativizing ingredient. -/
theorem idea38_ingredient_trivial : NonrelativizingIngredient (fun _ => True) :=
  ⟨fun _ => False, fun _ => false, trivial, id⟩

/-- (b) The "prove nothing" method trivially lacks one. -/
theorem idea38_not_ingredient : ¬ NonrelativizingIngredient (fun _ => False) :=
  fun ⟨_, _, h, _⟩ => h

/-- The obligation is equivalent to `Proves` accepting any oracle-dependent or false
statement; nothing ties `Proves` to a sound proof method about P vs NP. -/
theorem idea38_ingredient_of (Proves : ((Nat → Bool) → Prop) → Prop)
    (h : Proves (fun _ => False)) : NonrelativizingIngredient Proves :=
  ⟨fun _ => False, fun _ => false, h, id⟩
