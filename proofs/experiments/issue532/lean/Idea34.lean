/- Issue #532: 34_algorithm_quantifiers. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea34
theorem tested :
    ∃ fails : Bool → Bool → Prop,
      (∀ algorithm, ∃ input, fails algorithm input) ∧
      ¬ (∃ input, ∀ algorithm, fails algorithm input) := by
  refine ⟨(fun algorithm input => algorithm = input), ?_⟩
  decide
end Issue532.Idea34
