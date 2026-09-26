/- Issue #532: 27_variable_elimination. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea27
theorem tested (P Q : Prop) :
    (∃ b : Bool, (b = true ∧ P) ∨ (b = false ∧ Q)) ↔ P ∨ Q := by
  constructor
  · rintro ⟨b, h⟩
    rcases h with ⟨_, hp⟩ | ⟨_, hq⟩
    · exact Or.inl hp
    · exact Or.inr hq
  · intro h
    rcases h with hp | hq
    · exact ⟨true, Or.inl ⟨rfl, hp⟩⟩
    · exact ⟨false, Or.inr ⟨rfl, hq⟩⟩
end Issue532.Idea27
