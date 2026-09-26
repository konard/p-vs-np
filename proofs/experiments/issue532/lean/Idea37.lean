/- Issue #532: 37_parameter_bound. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea37
theorem tested (cost : Nat → Nat) (k cap : Nat)
    (monotone : ∀ a b, a ≤ b → cost a ≤ cost b)
    (bounded : k ≤ cap) : cost k ≤ cost cap := by
  exact monotone k cap bounded
end Issue532.Idea37
