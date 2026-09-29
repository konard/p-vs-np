import proofs.experiments.issue532.lean.Idea19
open Issue532.Idea19

/-- (a) Class parameters are free: with `NP := fun _ => True`, `PPoly := fun _ => False`
the obligation is one line. -/
theorem idea19_NPNotInPPoly_trivial : NPNotInPPoly (fun _ => True) (fun _ => False) :=
  ⟨fun _ => false, trivial, id⟩

/-- (b) ... and with `PPoly := fun _ => True` its negation is one line. -/
theorem idea19_not_NPNotInPPoly (NP : Lang → Prop) : ¬ NPNotInPPoly NP (fun _ => True) :=
  fun ⟨_, _, h⟩ => h trivial

/-- The conditional theorem then "separates" the trivial classes. -/
example : ¬ (∀ L : Lang, (fun _ => True) L → (fun _ => False) L) :=
  nonuniform_lower_bound_separates (fun _ => False) (fun _ => True) (fun _ => False)
    (fun _ h => h) idea19_NPNotInPPoly_trivial
