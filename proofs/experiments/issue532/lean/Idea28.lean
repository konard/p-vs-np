/- Issue #532: 28_definitional_extension. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea28
theorem tested (P : Prop) :
    (∃ z : Prop, (z ↔ P) ∧ z) ↔ P := by
  constructor
  · rintro ⟨_, hz, holds⟩
    exact hz.mp holds
  · intro hp
    exact ⟨P, Iff.rfl, hp⟩
end Issue532.Idea28
