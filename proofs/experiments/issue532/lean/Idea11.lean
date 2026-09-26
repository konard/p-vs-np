/- Issue #532: 11_relaxation_gap. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea11
def cost (n : Nat) : Nat := if n == 1 then 0 else 1
theorem tested : cost 1 < cost 0 ∧ cost 1 < cost 2 := by decide
end Issue532.Idea11
