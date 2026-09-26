/- Issue #532: 21_branching_exhaustive. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea21
theorem tested (P Q : Prop) :
    (P ∨ Q) ↔ ∃ b : Bool, if b then P else Q := by
  constructor
  · intro h
    rcases h with hp | hq
    · exact ⟨true, hp⟩
    · exact ⟨false, hq⟩
  · rintro ⟨b, h⟩
    cases b with
    | false => exact Or.inr h
    | true => exact Or.inl h
end Issue532.Idea21
