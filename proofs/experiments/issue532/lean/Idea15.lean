/- Issue #532: 15_size_vs_depth. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea15
inductive Shape where | chain | balanced
def size : Shape → Nat | .chain => 3 | .balanced => 3
def depth : Shape → Nat | .chain => 3 | .balanced => 2
theorem tested : size .chain = size .balanced ∧ depth .chain ≠ depth .balanced := by decide
end Issue532.Idea15
