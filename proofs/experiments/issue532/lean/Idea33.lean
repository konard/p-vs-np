/- Issue #532: 33_average_vs_worst. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea33
theorem tested :
    ∃ f : Bool × Bool → Bool,
      f (false, false) = false ∧ f (false, true) = true ∧
      f (true, false) = true ∧ f (true, true) = true := by
  exact ⟨(fun p => p.1 || p.2), by decide⟩
end Issue532.Idea33
