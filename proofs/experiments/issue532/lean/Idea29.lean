/- Issue #532: 29_reduction_correctness_chain. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea29
theorem tested {X Y : Type} (A : X → Prop) (B D : Y → Prop)
    (reduce : X → Y) (preserve : ∀ x, A x ↔ B (reduce x))
    (decideTarget : ∀ y, B y ↔ D y) :
    ∀ x, A x ↔ D (reduce x) := by
  intro x
  exact Iff.trans (preserve x) (decideTarget (reduce x))
end Issue532.Idea29
