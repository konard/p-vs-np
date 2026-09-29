(** Regression checks for the original Williams experiment. The actual
    framework is Idea41, over the shared Machine, Run and NAND circuits. *)

From Stdlib Require Import Lia List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.
From proofs.experiments.issue532.rocq Require Import Idea41.

Theorem no_zero_step : forall (m : Machine) (n : nat) (C : Circuit) (b : bool),
  ~ Run m (initial (encCircuit n C)) 0 b.
Proof.
  intros m n C b h. inversion h.
Qed.

(** A free Boolean answer function cannot act as a zero-step oracle. *)
Theorem no_zero_cost_oracle : forall answer : nat -> Circuit -> bool,
  ~ exists m : Machine, forall n C,
    Run m (initial (encCircuit n C)) 0 (answer n C).
Proof.
  intros answer [m hm]. exact (no_zero_step m 1 [] (answer 1 []) (hm 1 [])).
Qed.

(** Gate zero refers to non-existent wire one on a one-input circuit. *)
Theorem malformed_circuit_can_output_true :
  output [true] [(1, 0)] = true.
Proof. reflexivity. Qed.

Theorem malformed_circuit_rejected :
  CircuitSAT (encCircuit 1 [(1, 0)]) = false.
Proof.
  destruct (CircuitSAT (encCircuit 1 [(1, 0)])) eqn:h; [| reflexivity].
  apply circuitSAT_encode in h. destruct h as [hw _].
  unfold WF, WFfrom in hw. simpl in hw. lia.
Qed.
