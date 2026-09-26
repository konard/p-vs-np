/- Issue #532: 20_parallel_depth. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea20
def serial : Nat := 3 + 5
def independent : Nat := max 3 5
def dependent : Nat := 3 + 5
theorem tested : independent < serial ∧ dependent = serial := by decide
end Issue532.Idea20
