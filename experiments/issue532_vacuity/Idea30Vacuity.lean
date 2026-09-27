import proofs.experiments.issue532.lean.Idea30
open Issue532.Idea30

/-- (b) The class parameter `InNP` is free: for the empty class the obligation is
refutable. (For `InNP := fun _ => True` it becomes non-explicit Shannon counting,
true but not formalized here; the circuit-size measure itself is honest.) -/
theorem idea30_not_explicit_empty : ¬ ExplicitNPLowerBound (fun _ => False) :=
  fun ⟨_, hf, _⟩ => hf

/-- The truth of the obligation depends only on which `f` the predicate admits;
nothing ties `InNP` to NP. -/
theorem idea30_explicit_mono (P Q : (List Bool → Bool) → Prop) (hPQ : ∀ f, P f → Q f)
    (h : ExplicitNPLowerBound P) : ExplicitNPLowerBound Q :=
  let ⟨f, hf, hl⟩ := h; ⟨f, hPQ f hf, hl⟩
