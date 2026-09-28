import proofs.experiments.issue532.lean.Idea20
open Issue532.Idea20

/-- (a) `Realizable` is a free parameter: with `ResourceHonest` itself (or `False`)
as the realizability predicate the "postulate" is one line. -/
theorem idea20_honesty_trivial : PhysicalResourceHonesty ResourceHonest := fun _ h => h
theorem idea20_honesty_trivial' : PhysicalResourceHonesty (fun _ => False) := fun _ h => h.elim

/-- (b) With `Realizable := fun _ => True` its negation is one line (via the file's
own `dishonest_model_collapses`). -/
theorem idea20_not_honesty : ¬ PhysicalResourceHonesty (fun _ => True) := by
  intro h
  obtain ⟨m, _, _, _, hm⟩ := dishonest_model_collapses
  exact hm (h m trivial)
