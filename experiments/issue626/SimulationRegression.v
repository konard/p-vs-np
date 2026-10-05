From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.
From proofs.experiments.issue626.rocq Require Import Simulation Correctness.
Import ListNotations Complexity Simulation.

Check pSubsetPPoly : PSubsetPPoly.
Print Assumptions pSubsetPPoly.
Print Assumptions SimulationCorrectness.simCircuit_correct.

Definition clock (t : nat) : Polynomial := {| coefficient := t; degree := 0 |}.
Definition readBit : Machine :=
  {| program := [[halt false; halt false; halt true]] |}.
Example read_false : output [false] (simCircuit readBit (clock 1) 1) = false.
Proof. vm_compute. reflexivity. Qed.
Example read_true : output [true] (simCircuit readBit (clock 1) 1) = true.
Proof. vm_compute. reflexivity. Qed.

Definition readSecond : Machine := {| program :=
  [[move 1 blank right; move 1 blank right; move 1 blank right; move 1 blank right];
   [halt false; halt false; halt true; halt false]] |}.
Example second_true : output [false;true] (simCircuit readSecond (clock 2) 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example second_false : output [true;false] (simCircuit readSecond (clock 2) 2) = false.
Proof. vm_compute. reflexivity. Qed.
Example second_blank : output [true] (simCircuit readSecond (clock 2) 1) = false.
Proof. vm_compute. reflexivity. Qed.
Example second_beyond_clock : output [false;true] (simCircuit readSecond (clock 1) 2) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma second_run : Run readSecond (initial [false;true]) 2 true.
Proof. eapply run_next; [reflexivity | apply run_halt; reflexivity]. Qed.
Example no_short_run : ~ exists t b, t <= 1 /\ Run readSecond (initial [false;true]) t b.
Proof.
  intros [t [b [ht hr]]].
  destruct (run_deterministic _ _ _ _ _ _ second_run hr) as [he _]. lia.
Qed.

Example missing_column : output [true]
  (simCircuit {| program := [[halt true]] |} (clock 1) 1) = false.
Proof. vm_compute. reflexivity. Qed.

Definition acceptAll : Machine :=
  {| program := [[halt true; halt true; halt true; halt true]] |}.
Example early_halt : output [false] (simCircuit acceptAll (clock 3) 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example missing_row : output [true] (simCircuit {| program := [] |} (clock 3) 1) = false.
Proof. vm_compute. reflexivity. Qed.
Example zero_clock : output [true] (simCircuit acceptAll (clock 0) 1) = false.
Proof. vm_compute. reflexivity. Qed.

Definition writeSeparator : Machine := {| program :=
  [[move 1 separator right; move 1 separator right; move 1 separator right; move 1 separator right];
   [move 2 blank left; move 2 blank left; move 2 blank left; move 2 blank left];
   [halt false; halt false; halt false; halt true]] |}.
Example separator_roundtrip : output [false] (simCircuit writeSeparator (clock 3) 1) = true.
Proof. vm_compute. reflexivity. Qed.
Definition badState : Machine := {| program :=
  [[move 99 blank stay; move 99 blank stay; move 99 blank stay; move 99 blank stay]] |}.
Example missing_state : output [true] (simCircuit badState (clock 2) 1) = false.
Proof. vm_compute. reflexivity. Qed.

Example constant_cannot_simulate : forall C b,
  (forall x : Word, length x = 1 -> output x C = b) ->
  ~ (forall x t a, length x = 1 -> Run readBit (initial x) t a -> output x C = a).
Proof.
  intros C b hc hs.
  pose proof (hs [false] 1 false eq_refl (run_halt readBit (initial [false]) false eq_refl)) as hf.
  pose proof (hs [true] 1 true eq_refl (run_halt readBit (initial [true]) true eq_refl)) as ht.
  rewrite (hc [false] eq_refl) in hf. rewrite (hc [true] eq_refl) in ht. congruence.
Qed.

Definition loop : Machine := {| program := [[move 0 blank stay]] |}.
Lemma loop_no_run : forall t b, ~ Run loop (initial []) t b.
Proof.
  intros t b hr. remember (initial []) as c eqn:he.
  induction hr as [c b hs | c c' t b hs hr IH]; subst c.
  - discriminate hs.
  - change (@inr bool Config (initial []) = inr c') in hs. inversion hs; subst c'.
    apply IH. reflexivity.
Qed.
Example loop_not_classP : ~ exists P : ClassP, p_machine P = loop.
Proof.
  intros [P hp]. destruct (p_terminates P []) as [t [b [_ hr]]].
  rewrite hp in hr. exact (loop_no_run t b hr).
Qed.
