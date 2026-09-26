(** A conditional schema for syntactic independence using the shared P/NP
    definitions. No relation to ZFC is supplied or claimed. *)
From Stdlib Require Import Classical_Prop.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Record Theory := { proves : Prop -> Prop }.

Definition Independent (theory : Theory) (statement : Prop) : Prop :=
  ~ proves theory statement /\ ~ proves theory (~ statement).

Definition PvsNPIsIndependent (theory : Theory) : Prop :=
  Independent theory PEqualsNP.

Theorem independence_has_no_proof : forall theory,
  PvsNPIsIndependent theory ->
  ~ proves theory PEqualsNP /\ ~ proves theory PNotEqualsNP.
Proof. intros theory h. exact h. Qed.

Theorem pSubsetNP : forall p : ClassP, exists np : ClassNP,
  forall x : Word, p_language p x = np_language np x.
Proof.
  intro p. exists (pToNP p). intro x. reflexivity.
Qed.

Theorem pvsnpExcludedMiddle : PEqualsNP \/ PNotEqualsNP.
Proof. apply classic. Qed.

Print Assumptions pSubsetNP.
