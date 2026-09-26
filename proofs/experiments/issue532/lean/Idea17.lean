/- Issue #532: 17_enumeration_cost. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea17
def assignments : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
theorem tested : assignments.length = 4 := by decide
end Issue532.Idea17
