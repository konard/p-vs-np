(** A conditional schema for syntactic independence using the shared P/NP
    definitions. Statements are syntax, not semantic propositions. No proof
    relation for ZFC is supplied or claimed. *)
From Stdlib Require Import Classical_Prop.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Inductive Statement := pEqualsNP | neg (statement : Statement).

Fixpoint denotes (statement : Statement) : Prop :=
  match statement with
  | pEqualsNP => PEqualsNP
  | neg phi => ~ denotes phi
  end.

Record Theory := { proves : Statement -> Prop }.

Definition Provable (theory : Theory) (statement : Statement) : Prop :=
  proves theory statement.

Definition Independent (theory : Theory) (statement : Statement) : Prop :=
  ~ Provable theory statement /\ ~ Provable theory (neg statement).

Definition PvsNPIsIndependent (theory : Theory) : Prop :=
  Independent theory pEqualsNP.

Theorem independence_has_no_proof : forall theory,
  PvsNPIsIndependent theory ->
  ~ Provable theory pEqualsNP /\ ~ Provable theory (neg pEqualsNP).
Proof. intros theory h. exact h. Qed.

Theorem pSubsetNP : forall p : ClassP, exists np : ClassNP,
  forall x : Word, p_language p x = np_language np x.
Proof.
  intro p. exists (pToNP p). intro x. reflexivity.
Qed.

Theorem pvsnpExcludedMiddle : PEqualsNP \/ PNotEqualsNP.
Proof. apply classic. Qed.

Print Assumptions pSubsetNP.
