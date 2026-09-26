/- Issue #532: 23_resolution_soundness. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea23
theorem tested (P R S : Prop) (left : P ∨ R) (right : ¬ P ∨ S) :
    R ∨ S := by
  rcases left with hp | hr
  · rcases right with hnp | hs
    · exact False.elim (hnp hp)
    · exact Or.inr hs
  · exact Or.inl hr
end Issue532.Idea23
