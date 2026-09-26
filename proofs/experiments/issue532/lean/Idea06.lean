/- Issue #532: 06_local_minimum. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea06
def cost : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ => 0
theorem tested : cost 0 < cost 1 ∧ cost 2 < cost 0 := by decide
end Issue532.Idea06
