import proofs.p_vs_np_undecidable.lean.PvsNPUndecidable

open PvsNPUndecidable

-- The empty proof relation makes both syntactic nonprovability claims true.
def emptyTheory : Theory := ⟨fun _ => False⟩

example : PvsNPIsIndependent emptyTheory := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

example : Statement.denotes (.neg .pEqualsNP) = PNotEqualsNP := rfl

example (theory : Theory) (h : PvsNPIsIndependent theory) :
    ¬Provable theory (.neg .pEqualsNP) := h.2
