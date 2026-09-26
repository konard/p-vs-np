/- Issue #532: 08_finite_samples. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea08
def f (x : Bool) : Bool := x
def g (_ : Bool) : Bool := false
theorem tested : f false = g false ∧ f true ≠ g true := by decide
end Issue532.Idea08
