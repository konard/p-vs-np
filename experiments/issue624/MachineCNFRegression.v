From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import MachineCNF.
Import ListNotations Complexity Machines MachineCNF.

Definition dispatchProbe : Machine :=
  {| program := [[halt true; move 1 separator left]; [halt false]] |}.

Example missing_column_rejects :
  instructionCode (instruction dispatchProbe 0 one) = 0.
Proof. reflexivity. Qed.
Example left_separator_move :
  instructionCode (instruction dispatchProbe 0 zero) = 23.
Proof. reflexivity. Qed.
Example valid_move : evalCNF (dispatchAssignment dispatchProbe 7 0 zero)
  (dispatchCNF dispatchProbe 7) = true.
Proof. reflexivity. Qed.
Example valid_default : evalCNF (dispatchAssignment dispatchProbe 0 0 one)
  (dispatchCNF dispatchProbe 0) = true.
Proof. reflexivity. Qed.

Definition badInstruction : Assignment := fun v =>
  (v =? 7) || (v =? 10) || (v =? 13).
Example wrong_instruction_has_one_state :
  evalCNF badInstruction (LocalCNF.LocalCNF.oneHot 7 2) = true.
Proof. reflexivity. Qed.
Example wrong_instruction_has_one_symbol :
  evalCNF badInstruction (LocalCNF.LocalCNF.oneHot 9 4) = true.
Proof. reflexivity. Qed.
Example wrong_instruction_has_one_output :
  evalCNF badInstruction (LocalCNF.LocalCNF.oneHot 13 (instructionBound dispatchProbe)) = true.
Proof. reflexivity. Qed.
Example wrong_instruction_rejected :
  evalCNF badInstruction (dispatchCNF dispatchProbe 7) = false.
Proof. reflexivity. Qed.
Example multiple_values_rejected :
  evalCNF (fun _ => true) (dispatchCNF dispatchProbe 0) = false.
Proof. reflexivity. Qed.
Example missing_values_rejected :
  evalCNF (fun _ => false) (dispatchCNF dispatchProbe 0) = false.
Proof. reflexivity. Qed.
Example empty_table_rejected : ~ Satisfiable (dispatchCNF {| program := [] |} 0).
Proof. apply dispatchCNF_empty_unsatisfiable. Qed.

Example model_for_every_instruction : forall m base q s,
  q < length (program m) ->
  evalCNF (dispatchAssignment m base q s) (dispatchCNF m base) = true.
Proof. exact dispatchAssignment_models. Qed.

Example unary_size : forall m base,
  length (encodeCNF (dispatchCNF m base)) <=
    2 * (length (program m) * length (program m) + 4 * length (program m) +
      instructionBound m * instructionBound m + 19) *
      (1 + (length (program m) + instructionBound m + 7) *
        (base + length (program m) + instructionBound m + 5)).
Proof. exact dispatchCNF_encoded_size. Qed.

Print Assumptions dispatchCNF_models.
Print Assumptions dispatchAssignment_models.
Print Assumptions instructionCode_injective.
Print Assumptions dispatchCNF_encoded_size.
Print Assumptions dispatchCNF_instruction.
Print Assumptions dispatchCNF_step.
Print Assumptions dispatchCNF_wrong_instruction.
Print Assumptions dispatchCNF_polynomial_size.

Example polynomial_offset : forall m p n base, base <= evalPoly p n ->
  length (encodeCNF (dispatchCNF m base)) <= evalPoly (dispatchPolynomial m p) n.
Proof. exact dispatchCNF_polynomial_size. Qed.

Example distinct_next_states : forall w d,
  instructionCode (move 17 w d) <> instructionCode (move 18 w d).
Proof.
  intros w d h. apply instructionCode_injective in h. discriminate.
Qed.
