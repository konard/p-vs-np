/- Issue #532: 39_proof_system_scope. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea39
theorem tested :
    ∃ weak strong : Bool → Prop,
      (∀ proof, weak proof → strong proof) ∧
      (∀ proof, ¬ weak proof) ∧ (∃ proof, strong proof) := by
  refine ⟨(fun _ => False), (fun _ => True), ?_, ?_, ?_⟩
  · intro _ impossible
    exact False.elim impossible
  · intro _ impossible
    exact impossible
  · exact ⟨false, True.intro⟩
end Issue532.Idea39
