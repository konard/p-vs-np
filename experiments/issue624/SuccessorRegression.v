From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import SuccessorCNF.
Import ListNotations Complexity Machines SuccessorCNF.

Definition regression_machine : Machine :=
  Build_Machine [[move 0 one right; move 0 one right; move 0 one right; halt false]].
Definition regression_before : Config := Build_Config 0 [blank] zero [blank].
Definition regression_after : Config := moveHead regression_before 0 one right.
Definition regression_wrong_write : Config := moveHead regression_before 0 zero right.
Definition regression_assignment (d : Config) : Assignment :=
  fun v => orb (rowAssignment 0 1 3 regression_before v) (rowAssignment 20 1 3 d v).

Example valid_successor : evalCNF (regression_assignment regression_after)
  (successorCNF regression_machine 0 20 3) = true.
Proof. reflexivity. Qed.

Definition regression_direction (dir : Direction) : Machine :=
  Build_Machine [[move 0 one dir; move 0 one dir; move 0 one dir; move 0 one dir]].
Example valid_left : evalCNF (regression_assignment (moveHead regression_before 0 one left))
  (successorCNF (regression_direction left) 0 20 3) = true.
Proof. reflexivity. Qed.
Example valid_stay : evalCNF (regression_assignment (moveHead regression_before 0 one stay))
  (successorCNF (regression_direction stay) 0 20 3) = true.
Proof. reflexivity. Qed.

Definition regression_wrong_copy : Config := Build_Config 0 [one; one] blank [].
Example wrong_copy_rows_valid : evalCNF (regression_assignment regression_wrong_copy)
  (rowCNF 0 1 3 ++ rowCNF 20 1 3) = true.
Proof. reflexivity. Qed.
Example wrong_copy_rejected : evalCNF (regression_assignment regression_wrong_copy)
  (successorCNF regression_machine 0 20 3) = false.
Proof. reflexivity. Qed.
Example row_decode : decodeRow (rowAssignment 0 1 3 regression_before) 0 1 3 = regression_before.
Proof. reflexivity. Qed.
Example missing_selections : evalCNF (fun _ => false) (rowCNF 0 1 3) = false.
Proof. reflexivity. Qed.
Example multiple_selections : evalCNF (fun _ => true) (rowCNF 0 1 3) = false.
Proof. reflexivity. Qed.
Example empty_machine : evalCNF (regression_assignment regression_after)
  (successorCNF (Build_Machine []) 0 20 3) = false.
Proof. reflexivity. Qed.
Example empty_window : evalCNF (regression_assignment regression_after)
  (successorCNF regression_machine 0 20 0) = false.
Proof. reflexivity. Qed.
Example accepting_halt_is_no_move : evalCNF (regression_assignment regression_after)
  (successorCNF (Build_Machine [[halt true; halt true; halt true; halt true]]) 0 20 3) = false.
Proof. reflexivity. Qed.
Example invalid_target : evalCNF (regression_assignment regression_after)
  (successorCNF (Build_Machine [[move 1 one right; move 1 one right]]) 0 20 3) = false.
Proof. reflexivity. Qed.

Definition regression_two_states : Machine :=
  Build_Machine [[move 1 one right; move 1 one right]; [halt true]].
Definition regression_assignment_two (d : Config) : Assignment :=
  fun v => orb (rowAssignment 0 2 3 regression_before v) (rowAssignment 20 2 3 d v).
Example valid_state_change : evalCNF
  (regression_assignment_two (moveHead regression_before 1 one right))
  (successorCNF regression_two_states 0 20 3) = true.
Proof. reflexivity. Qed.
Example wrong_state_rows_valid : evalCNF (regression_assignment_two regression_after)
  (rowCNF 0 2 3 ++ rowCNF 20 2 3) = true.
Proof. reflexivity. Qed.
Example wrong_state_rejected : evalCNF (regression_assignment_two regression_after)
  (successorCNF regression_two_states 0 20 3) = false.
Proof. reflexivity. Qed.

Definition regression_right_edge : Config := Build_Config 0 [blank; blank] zero [].
Example right_window_edge_rejected : evalCNF
  (fun v => orb (rowAssignment 0 1 3 regression_right_edge v)
    (rowAssignment 20 1 3 regression_before v))
  (successorCNF regression_machine 0 20 3) = false.
Proof. reflexivity. Qed.

Example wrong_write_rows_valid : evalCNF (regression_assignment regression_wrong_write)
  (rowCNF 0 1 3 ++ rowCNF 20 1 3) = true.
Proof. reflexivity. Qed.
Example wrong_write_rejected : evalCNF (regression_assignment regression_wrong_write)
  (successorCNF regression_machine 0 20 3) = false.
Proof. reflexivity. Qed.
Example wrong_head_rejected : evalCNF (regression_assignment regression_before)
  (successorCNF regression_machine 0 20 3) = false.
Proof. reflexivity. Qed.
Example encoded_length : length (encodeCNF (successorCNF regression_machine 0 20 3)) <=
  successorSize regression_machine 0 20 3.
Proof. apply successorCNF_encoded_size. Qed.
Example default_rejection : evalCNF (regression_assignment regression_after)
  (successorCNF (Build_Machine [[]]) 0 20 3) = false.
Proof. reflexivity. Qed.

Example left_flatten : flatten (moveHead regression_before 0 one left) =
  setCell (flatten regression_before) (length (tapeLeft regression_before)) one.
Proof. reflexivity. Qed.
Example stay_flatten : flatten (moveHead regression_before 0 one stay) =
  setCell (flatten regression_before) (length (tapeLeft regression_before)) one.
Proof. reflexivity. Qed.

Definition regression_edge : Config := Build_Config 0 [] zero [blank; blank].
Definition regression_left : Machine := Build_Machine [[move 0 one left; move 0 one left]].
Example edge_step_exists : step regression_left regression_edge =
  inr (moveHead regression_edge 0 one left).
Proof. reflexivity. Qed.
Example window_edge_rejected : evalCNF
  (fun v => orb (rowAssignment 0 1 3 regression_edge v)
    (rowAssignment 20 1 3 regression_before v))
  (successorCNF regression_left 0 20 3) = false.
Proof. reflexivity. Qed.

Print Assumptions rowAssignment_represents.
Print Assumptions rowCNF_models.
Print Assumptions decodeRow_represents.
Print Assumptions moveHead_matches.
Print Assumptions transitionCNF_step.
Print Assumptions successorCNF_models.
Print Assumptions successorCNF_sound.
Print Assumptions successorCNF_decoded_wrong_successor.
Print Assumptions successorCNF_encoded_size.
