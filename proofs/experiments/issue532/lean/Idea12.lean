/- Issue #532: 12_reduction_soundness. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea12
def source (x : Bool) : Bool := x
def target (x : Bool) : Bool := x
def badMap (_ : Bool) : Bool := true
theorem tested : source false ≠ target (badMap false) := by decide
end Issue532.Idea12
