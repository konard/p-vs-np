/- Issue #532: 04_pairwise_consistency. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea04
def allConstraints (x y z : Bool) : Bool := (x != y) && (y != z) && (x != z)
theorem tested : ∀ x y z : Bool, allConstraints x y z = false := by decide
end Issue532.Idea04
