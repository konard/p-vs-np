/- Issue #532: 09_length_vs_runtime. Finite model only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea09
inductive Program where | short | long
def length : Program → Nat | .short => 1 | .long => 2
def steps : Program → Nat | .short => 10 | .long => 1
theorem tested : length .short < length .long ∧ steps .long < steps .short := by decide
end Issue532.Idea09
