/- Issue #532: 14_random_seed. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea14
def randomizedAnswer (seed : Bool) : Bool := seed
theorem tested : randomizedAnswer true = true ∧ randomizedAnswer false = false := by decide
end Issue532.Idea14
