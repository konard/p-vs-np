/- Issue #532: 05_greedy_choice. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea05
def greedyCost : Nat := 1 + 10
def alternativeCost : Nat := 2 + 1
theorem tested : alternativeCost < greedyCost := by decide
end Issue532.Idea05
