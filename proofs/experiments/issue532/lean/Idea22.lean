/- Issue #532: 22_decision_guides_search. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea22
theorem tested (P Q : Prop) (b : Bool)
    (oracle : b = true ↔ P) (hasWitness : P ∨ Q) :
    if b then P else Q := by
  cases b with
  | false =>
      have notP : ¬ P := by
        intro hp
        have impossible := oracle.mpr hp
        cases impossible
      exact Or.resolve_left hasWitness notP
  | true => exact oracle.mp rfl
end Issue532.Idea22
