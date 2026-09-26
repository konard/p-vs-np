/- Issue #532: 30_lower_bound_transfer. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea30
theorem tested {Algorithm Circuit : Type}
    (compile : Algorithm → Circuit) (fast : Algorithm → Prop)
    (correct expensive : Circuit → Prop)
    (lowerBound : ∀ c, correct c → expensive c)
    (simulation : ∀ a, fast a → correct (compile a))
    (sizeBound : ∀ a, fast a → ¬ expensive (compile a)) :
    ∀ a, ¬ fast a := by
  intro a ha
  exact (sizeBound a ha) (lowerBound (compile a) (simulation a ha))
end Issue532.Idea30
