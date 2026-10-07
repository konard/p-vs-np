import proofs.experiments.issue624.lean.MachineCNF

open Complexity Issue532.Machines Issue624.MachineCNF

def dispatchProbe : Machine :=
  ⟨[[.halt true, .move 1 .separator .left], [.halt false]]⟩

-- A missing column uses the shared default rejecting instruction.
example : instructionCode (dispatchProbe.instruction 0 .one) = 0 := by decide
example : instructionCode (dispatchProbe.instruction 0 .zero) = 23 := by decide

example : evalCNF (dispatchAssignment dispatchProbe 7 0 .zero)
    (dispatchCNF dispatchProbe 7) = true := dispatchAssignment_models _ _ _ _ (by decide)
example : evalCNF (dispatchAssignment dispatchProbe 0 0 .one)
    (dispatchCNF dispatchProbe 0) = true := dispatchAssignment_models _ _ _ _ (by decide)

-- The state and scanned-symbol bits are correct, but the output instruction
-- is changed from a move to rejection. Exactly-one constraints alone pass.
def badInstruction : Assignment := fun v => v == 7 || v == 10 || v == 13
example : evalCNF badInstruction (Issue624.LocalCNF.oneHot 7 2) = true := by
  apply (oneHot_selected _ _ _).mpr
  exact ⟨0, by simp [Selected, badInstruction]; omega⟩
example : evalCNF badInstruction (Issue624.LocalCNF.oneHot 9 4) = true := by
  apply (oneHot_selected _ _ _).mpr
  exact ⟨1, by simp [Selected, badInstruction]; omega⟩
example : evalCNF badInstruction (Issue624.LocalCNF.oneHot 13 (instructionBound dispatchProbe)) = true := by
  apply (oneHot_selected _ _ _).mpr
  exact ⟨0, by simp [Selected, badInstruction, dispatchProbe, instructionBound,
    instructionCodes, symbols, Machine.instruction, instructionCode, Symbol.index, directionCode]; omega⟩
example : evalCNF badInstruction (dispatchCNF dispatchProbe 7) = false := by
  apply dispatchCNF_wrong_instruction dispatchProbe 7 badInstruction 0 0 .zero
  all_goals simp [Selected, badInstruction, dispatchProbe, instructionBound,
    instructionCodes, symbols, Machine.instruction, instructionCode,
    Symbol.index, directionCode] <;> omega
example : evalCNF (fun _ => true) (dispatchCNF dispatchProbe 0) = false := by decide
example : evalCNF (fun _ => false) (dispatchCNF dispatchProbe 0) = false := by decide
example : ¬ Satisfiable (dispatchCNF ⟨[]⟩ 0) := by
  exact dispatchCNF_empty_unsatisfiable 0

example (m : Machine) (base q : Nat) (s : Symbol) (hq : q < m.program.length) :
    evalCNF (dispatchAssignment m base q s) (dispatchCNF m base) = true :=
  dispatchAssignment_models m base q s hq

example (m : Machine) (base : Nat) :
    (encodeCNF (dispatchCNF m base)).length ≤
      2 * (m.program.length * m.program.length + 4 * m.program.length +
        (instructionBound m) * (instructionBound m) + 19) *
        (1 + (m.program.length + instructionBound m + 7) *
          (base + m.program.length + instructionBound m + 5)) :=
  dispatchCNF_encoded_size m base

#print axioms dispatchCNF_models
#print axioms dispatchAssignment_models
#print axioms instructionCode_injective
#print axioms dispatchCNF_encoded_size
#print axioms dispatchCNF_instruction
#print axioms dispatchCNF_step
#print axioms dispatchCNF_wrong_instruction
#print axioms dispatchCNF_polynomial_size

example (m : Machine) (p : Polynomial) (n base : Nat) (hb : base ≤ p.eval n) :
    (encodeCNF (dispatchCNF m base)).length ≤ (dispatchPolynomial m p).eval n :=
  dispatchCNF_polynomial_size m p n base hb

-- Finite coverage of every symbol and direction with distinct next states.
example (w : Symbol) (d : Direction) :
    instructionCode (.move 17 w d) ≠ instructionCode (.move 18 w d) := by
  intro h
  have he := instructionCode_injective _ _ h
  cases he
