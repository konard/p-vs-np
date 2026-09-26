/- Issue #532: 24_unit_propagation. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea24
theorem tested (P Q : Prop) (unit : P) (clause : ¬ P ∨ Q) : Q := by
  rcases clause with hnp | hq
  · exact False.elim (hnp unit)
  · exact hq
end Issue532.Idea24
