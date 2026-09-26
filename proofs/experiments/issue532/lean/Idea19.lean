/- Issue #532: 19_answer_as_advice. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea19
def advice (x : Bool) : Bool := x
def solver (_x hint : Bool) : Bool := hint
theorem tested : ∀ x : Bool, solver x (advice x) = x := by decide
end Issue532.Idea19
