/- Issue #532: 40_size_induction. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea40
theorem tested (P : Nat → Prop) (base : P 0)
    (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih
end Issue532.Idea40
