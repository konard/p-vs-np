From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import RunCNF.
Import ListNotations Complexity Machines Tableau RunCNF.

Definition accept : Machine := {| program := [[halt true; halt true; halt true; halt true]] |}.
Definition reject : Machine := {| program := [[halt false; halt false; halt false; halt false]] |}.
Definition startSensitive : Machine := {| program :=
  [[halt false; halt false; halt false; halt false]; [halt true; halt true; halt true; halt true]] |}.
Definition first : Config := {| state := 0; tapeLeft := [blank]; tapeHead := blank; tapeRight := [blank] |}.
Definition last : Config := {| state := 1; tapeLeft := [blank]; tapeHead := blank; tapeRight := [blank] |}.
Definition wrong : Config := {| state := 1; tapeLeft := [blank]; tapeHead := one; tapeRight := [blank] |}.
Definition model m trace : Assignment := traceAssignment 7 (length (program m)) 3 trace.

Example immediate : evalCNF (model accept [first]) (runCNF accept 7 3 1) = true. Proof. vm_compute. reflexivity. Qed.
Example inactive_suffix : evalCNF (model accept [first]) (runCNF accept 7 3 3) = true. Proof. vm_compute. reflexivity. Qed.
Example arbitrary_suffix : evalCNF (fun v => if v <? nextBase 7 1 3 then model accept [first] v else true)
  (runCNF accept 7 3 3) = true. Proof. vm_compute. reflexivity. Qed.
Example zero_clock : evalCNF (model accept [first]) (runCNF accept 7 3 0) = false. Proof. vm_compute. reflexivity. Qed.
Example rejecting : evalCNF (model reject [first]) (runCNF reject 7 3 3) = false. Proof. vm_compute. reflexivity. Qed.
(* Initial-row wiring is essential even for a verifier rejecting every input. *)
Example rejecting_initial : step startSensitive (initial []) = inl false. Proof. reflexivity. Qed.
Example rejecting_state_zero : evalCNF (model startSensitive [first]) (runCNF startSensitive 7 3 1) = false. Proof. vm_compute. reflexivity. Qed.
Example unrelated_accepting_state : evalCNF (model startSensitive [last]) (runCNF startSensitive 7 3 1) = true. Proof. vm_compute. reflexivity. Qed.
Example premature_halt : evalCNF (model accept [first; first]) (runCNF accept 7 3 3) = false. Proof. vm_compute. reflexivity. Qed.
Example two_steps : evalCNF (model moveThenAccept [first; last]) (runCNF moveThenAccept 7 3 2) = true. Proof. vm_compute. reflexivity. Qed.
Example short_clock : evalCNF (model moveThenAccept [first; last]) (runCNF moveThenAccept 7 3 1) = false. Proof. vm_compute. reflexivity. Qed.
Example missing_halt : evalCNF (model moveThenAccept [first]) (runCNF moveThenAccept 7 3 2) = false. Proof. vm_compute. reflexivity. Qed.
Example wrong_successor : evalCNF (model moveThenAccept [first; wrong]) (runCNF moveThenAccept 7 3 2) = false. Proof. vm_compute. reflexivity. Qed.
Example decoded : decodeTrace moveThenAccept 7 3 2 (model moveThenAccept [first; last]) = [first; last]. Proof. vm_compute. reflexivity. Qed.
Example missing_selection : evalCNF (fun _ => false) (runCNF accept 7 3 1) = false. Proof. vm_compute. reflexivity. Qed.
Example multiple_selection : evalCNF (fun _ => true) (runCNF accept 7 3 1) = false. Proof. vm_compute. reflexivity. Qed.
Example empty_machine : evalCNF (fun _ => true) (runCNF {| program := [] |} 7 3 1) = false. Proof. vm_compute. reflexivity. Qed.
Example empty_window : evalCNF (fun _ => true) (runCNF accept 7 0 1) = false. Proof. vm_compute. reflexivity. Qed.
Example rejecting_unsatisfiable : ~ Satisfiable (runCNF reject 7 3 3).
Proof.
  apply runCNF_rejecting_unsatisfiable. intros [q l s r]. destruct q as [|q].
  - destruct s; reflexivity.
  - unfold step. rewrite instruction_of_length_le; [reflexivity|simpl; lia].
Qed.
Example encoded_size : length (encodeCNF (runCNF moveThenAccept 7 3 2)) <= runSize moveThenAccept 7 3 2.
Proof. apply runCNF_encoded_size. Qed.
Example polynomial_size : length (encodeCNF (runCNF moveThenAccept 7 3 2)) <=
  evalPoly (runPolynomial moveThenAccept {| coefficient := 7; degree := 0 |}
    {| coefficient := 3; degree := 0 |} {| coefficient := 2; degree := 0 |}) 0.
Proof. apply runCNF_polynomial_size; vm_compute; lia. Qed.

Print Assumptions runCNF_sound.
Print Assumptions runCNF_complete.
Print Assumptions runCNF_models.
Print Assumptions runCNF_wrong_successor_rejected.
Print Assumptions runCNF_encoded_size.
Print Assumptions runCNF_polynomial_size.
Print Assumptions runCNF_rejecting_unsatisfiable.
