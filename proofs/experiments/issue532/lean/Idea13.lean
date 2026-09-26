/- Issue #532: 13_approximation_gap. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea13
def optimum : Nat := 3
def approximate : Nat := 4
theorem tested : approximate ≤ 2 * optimum ∧ approximate ≠ optimum := by decide
end Issue532.Idea13
