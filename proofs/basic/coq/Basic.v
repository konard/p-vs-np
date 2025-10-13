(**
  Basic.v - Simple foundational proofs in Coq

  This file serves as a bootstrap for formal verification in Coq,
  demonstrating basic proof techniques and serving as a template for
  future P vs NP related proofs.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(** * Basic Logical Proofs *)

Theorem modus_ponens : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  apply HPQ.
  exact HP.
Qed.

Theorem and_commutative : forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.

Theorem or_commutative : forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. exact HP.
  - left. exact HQ.
Qed.

(** * Basic Arithmetic Proofs *)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall m n : nat, m + n = n + m.
Proof.
  intros m n.
  induction m as [| m' IHm'].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem mul_1_r : forall n : nat, n * 1 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc : forall a b c : nat, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  - reflexivity.
  - simpl. rewrite IHa'. reflexivity.
Qed.

(** * Even Numbers (useful for complexity theory) *)

Definition isEven (n : nat) : Prop := exists k, n = 2 * k.

Theorem double_is_even : forall n : nat, isEven (2 * n).
Proof.
  intro n.
  unfold isEven.
  exists n.
  reflexivity.
Qed.

(** * Factorial Function *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Theorem factorial_pos : forall n : nat, 0 < factorial n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. auto with arith.
  - simpl.
    (* (S n') * factorial n' > 0 because both factors > 0 *)
    destruct (factorial n') as [| fn'].
    + (* factorial n' = 0 contradicts IHn' *)
      inversion IHn'.
    + (* factorial n' = S fn', so product > 0 *)
      simpl. auto with arith.
Qed.

(** * List Operations (relevant for algorithm complexity) *)

Theorem list_length_append : forall {A : Type} (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(** * Identity and Reflexivity *)

Theorem refl_eq : forall {A : Type} (x : A), x = x.
Proof.
  intros A x.
  reflexivity.
Qed.

(** * Verification Checks *)

Check modus_ponens.
Check add_comm.
Check factorial_pos.
Check list_length_append.

(** All basic Coq proofs verified successfully *)
