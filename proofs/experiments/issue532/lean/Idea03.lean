/- Issue #532: 03_verifier_soundness. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea03
def verify (x y : Bool) : Bool := x && y
theorem tested : ∀ x y : Bool, verify x y = true → x = true ∧ y = true := by decide
end Issue532.Idea03
