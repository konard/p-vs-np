/- Issue #532: 36_exact_rounding. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea36
theorem tested {Discrete Relaxed : Type}
    (feasible : Discrete → Prop) (relaxed : Relaxed → Prop)
    (round : Relaxed → Discrete)
    (soundRound : ∀ y, relaxed y → feasible (round y)) :
    (∃ y, relaxed y) → ∃ x, feasible x := by
  rintro ⟨y, hy⟩
  exact ⟨round y, soundRound y hy⟩
end Issue532.Idea36
