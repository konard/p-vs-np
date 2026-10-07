import proofs.experiments.issue624.lean.Arithmetic

open Complexity Issue532.Machines Issue624.RegisterMachine

-- A single composition covers equal operands, truncated subtraction, both
-- comparison outcomes, both branches, scratch cleanup, and existing output.
def arithmeticRegression : Program :=
  .sequence (mulProgram 0 0 2)
    (.sequence (ltProgram 0 1 3)
      (.sequence (eqProgram 0 0 4)
        (.sequence (eqProgram 0 1 5)
          (.sequence (branchProgram 3 12 (.straight (.emit [false])) (.straight (.emit [true])))
            (branchProgram 5 12 (.straight (.emit [true])) (.straight (.emit [false])))))))

set_option maxRecDepth 2048 in
example : programRun arithmeticRegression
    ⟨[2, 3, 9, 9, 9, 9] ++ List.replicate 20 7, [false, true]⟩ =
    ⟨[2, 3, 4, 0, 1, 0] ++ List.replicate 7 0 ++ List.replicate 13 7, [false, true, false, false]⟩ := rfl

example : ProgramWellFormed 26 arithmeticRegression := by decide

#print axioms mulProgram_registers
#print axioms ltProgram_registers
#print axioms eqProgram_registers
#print axioms ifLtProgram_run
#print axioms selectEqProgram_run
