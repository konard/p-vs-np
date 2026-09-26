/- Issue #532: 10_monotone_boundary. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea10
def negation (x : Bool) : Bool := !x
theorem tested : negation false = true ∧ negation true = false := by decide
end Issue532.Idea10
