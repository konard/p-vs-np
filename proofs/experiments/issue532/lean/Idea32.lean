/- Issue #532: 32_promise_coverage. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea32
theorem tested :
    ∃ promise answer : Bool → Bool,
      (∀ x, promise x = true → answer x = x) ∧ answer false ≠ false := by
  refine ⟨(fun x => x), (fun _ => true), ?_, ?_⟩
  · intro x hx
    cases x <;> cases hx <;> rfl
  · decide
end Issue532.Idea32
