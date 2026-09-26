/- Issue #532: 18_restricted_instance. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea18
def easy (x : Bool) : Bool := x || true
def general (x y : Bool) : Bool := x || y
theorem tested : (∀ x : Bool, easy x = true) ∧ general false false = false := by decide
end Issue532.Idea18
