(* Logical tests of Vega (2015), Definition 3.1 and Theorems 5.3/6.2.
   No complexity bounds are represented in this finite toy model. *)
From Stdlib Require Import Arith Bool Lia.

Module VegaRefutation.

(* A shared certificate can encode the diagonal by agreeing with both inputs.
   Thus certificate-ignoring verifiers do not refute Theorem 6.1. *)
Definition shared_verifier (d : nat -> bool) (x z : nat) : bool :=
  d x && Nat.eqb z x.

Theorem diagonal_has_shared_certificate :
  forall (d : nat -> bool) x y,
    (x = y /\ d x = true) <->
    (exists z, shared_verifier d x z = true /\
               shared_verifier d y z = true).
Proof.
  intros d x y; split.
  - intros [Hxy Hx]; subst y.
    exists x; unfold shared_verifier.
    rewrite Hx, Nat.eqb_refl; auto.
  - intros [z [Hx Hy]].
    unfold shared_verifier in Hx, Hy.
    apply andb_true_iff in Hx.
    apply andb_true_iff in Hy.
    destruct Hx as [Hdx Hzx].
    destruct Hy as [_ Hzy].
    apply Nat.eqb_eq in Hzx.
    apply Nat.eqb_eq in Hzy.
    split; [lia | exact Hdx].
Qed.

Definition diagonal (L : nat -> Prop) (p : nat * nat) : Prop :=
  fst p = snd p /\ L (fst p).
Definition constant (_ : nat) : nat := 0.

(* A non-injective single-string reduction applied to both pair coordinates
   does not automatically preserve the diagonal predicate. *)
Theorem naive_diagonal_reduction_fails :
  ~ diagonal (fun _ => True) (0, 1) /\
  diagonal (fun _ => True) (constant 0, constant 1).
Proof.
  split.
  - unfold diagonal; simpl; intros [H _]; discriminate H.
  - unfold diagonal, constant; simpl; auto.
Qed.

Definition smallP (x : nat) : Prop := x = 0.
Definition smallNP (x : nat) : Prop := x = 0 \/ x = 1.
Definition commonClass (x : nat) : Prop := x = 0 \/ x = 1.

(* Concrete countermodel to the inclusion-to-equality inference. This is
   not an interpretation of the actual P and NP complexity classes. *)
Theorem two_inclusions_do_not_give_equality :
  (forall x, smallP x -> commonClass x) /\
  (forall x, smallNP x -> commonClass x) /\
  (exists x, smallNP x /\ ~ smallP x).
Proof.
  split.
  - unfold smallP, commonClass; intros; auto.
  - split.
    + unfold smallNP, commonClass; auto.
    + exists 1; unfold smallNP, smallP; lia.
Qed.

End VegaRefutation.
