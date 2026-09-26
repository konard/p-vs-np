/- Issue #532: 38_oracle_worlds. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea38
theorem tested :
    ∃ property : Bool → Prop, property false ∧ ¬ property true := by
  refine ⟨(fun oracle => oracle = false), rfl, ?_⟩
  decide
end Issue532.Idea38
