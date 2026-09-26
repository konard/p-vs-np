/- Issue #532: 01_bounded_sat. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea01
def sat (x y : Bool) : Bool := x && !y
def search : Bool := sat false false || sat false true || sat true false || sat true true
theorem tested : search = true := by decide
end Issue532.Idea01
