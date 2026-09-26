/- Issue #532: 25_independent_components. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea25
theorem tested {X Y : Type} (A : X → Prop) (B : Y → Prop) :
    (∃ x, A x) ∧ (∃ y, B y) ↔ ∃ x y, A x ∧ B y := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x, y, hx, hy⟩
  · rintro ⟨x, y, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
end Issue532.Idea25
