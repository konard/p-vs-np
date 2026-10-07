From Stdlib Require Import List Bool Arith.
From proofs.experiments.issue624.rocq Require Import Arithmetic.
Import ListNotations Complexity Machines RegisterMachine Arithmetic.

Definition arithmeticRegression : Program :=
  sequence (mulProgram 0 0 2)
    (sequence (ltProgram 0 1 3)
      (sequence (eqProgram 0 0 4)
        (sequence (eqProgram 0 1 5)
          (sequence (branchProgram 3 12 (straight (emit [false])) (straight (emit [true])))
            (branchProgram 5 12 (straight (emit [true])) (straight (emit [false]))))))).

Example arithmetic_composition : programRun arithmeticRegression
    (mkState ([2; 3; 9; 9; 9; 9] ++ repeat 7 20) [false; true]) =
    mkState ([2; 3; 4; 0; 1; 0] ++ repeat 0 7 ++ repeat 7 13) [false; true; false; false].
Proof. reflexivity. Qed.

Print Assumptions mulProgram_registers.
Print Assumptions ltProgram_registers.
Print Assumptions eqProgram_registers.
Print Assumptions ifLtProgram_run.
Print Assumptions selectEqProgram_run.
