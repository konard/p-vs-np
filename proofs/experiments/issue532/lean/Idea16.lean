/- Issue #532: 16_finite_diagonal. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea16
def first (_ : Bool) : Bool := false
def second (_ : Bool) : Bool := true
def diagonal (x : Bool) : Bool := !x
theorem tested : diagonal false ≠ first false ∧ diagonal true ≠ second true := by decide
end Issue532.Idea16
