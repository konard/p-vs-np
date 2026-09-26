/- Issue #532: 07_lossy_compression. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea07
def encode (p : Bool × Bool) : Bool := p.1
theorem tested : encode (false, false) = encode (false, true) ∧ (false, false) ≠ (false, true) := by decide
end Issue532.Idea07
