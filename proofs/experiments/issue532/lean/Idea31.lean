/- Issue #532: 31_lengthwise_advice. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea31
theorem tested (f : Bool → Bool) :
    ∃ table : Bool × Bool, f false = table.1 ∧ f true = table.2 := by
  exact ⟨(f false, f true), rfl, rfl⟩
end Issue532.Idea31
