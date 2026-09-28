import proofs.experiments.issue532.lean.Idea23
open Issue532.Idea23

/-- (a) `Efficient` is a free parameter: with `fun _ => False` the lower bound is one line. -/
theorem idea23_noPolyBounded_trivial : NoPolyBoundedProofSystem (fun _ => False) :=
  fun _ h => h.elim

/-- (b) With `fun _ => True` its negation (already `unrestricted_obligation_false`). -/
theorem idea23_not_noPolyBounded : ¬ NoPolyBoundedProofSystem (fun _ => True) :=
  unrestricted_obligation_false

/-- The conditional theorem then "excludes" every efficient decider of the trivial class. -/
example : ∀ dec, Decides dec → ¬ (fun _ => False) dec :=
  lower_bound_excludes_efficient_decider (fun _ => False) (fun _ => False)
    (fun _ _ h => h) idea23_noPolyBounded_trivial
