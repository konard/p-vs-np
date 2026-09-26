/- Issue #532: 02_failed_certificate. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea02
def sat (x y : Bool) : Bool := x && !y
def search : Bool := sat false false || sat false true || sat true false || sat true true
theorem tested : sat true true = false ∧ search = true := by decide
end Issue532.Idea02
