/- Issue #532: 26_separator_agreement. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea26
theorem tested :
    (∃ b : Bool, b = true) ∧ (∃ b : Bool, b = false) ∧
    ¬ (∃ b : Bool, b = true ∧ b = false) := by decide
end Issue532.Idea26
