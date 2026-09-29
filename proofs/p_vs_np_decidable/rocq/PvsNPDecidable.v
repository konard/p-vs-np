(** Classical excluded middle applied to the finite machine P/NP question.
    This does not provide an algorithm or settle the question. *)
From Stdlib Require Import Classical_Prop.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Definition is_decidable (P : Prop) : Prop := P \/ ~ P.

Theorem P_vs_NP_is_decidable : PEqualsNP \/ PNotEqualsNP.
Proof. apply classic. Qed.

Theorem P_vs_NP_decidable : is_decidable PEqualsNP.
Proof. unfold is_decidable. apply classic. Qed.

Theorem P_vs_NP_has_answer : PEqualsNP \/ ~ PEqualsNP.
Proof. apply classic. Qed.

Theorem pSubsetNP : forall p : ClassP, exists np : ClassNP,
  forall x : Word, p_language p x = np_language np x.
Proof.
  intro p. exists (pToNP p). intro x. reflexivity.
Qed.

Definition pvsnpIsWellFormed : Prop := PEqualsNP \/ PNotEqualsNP.

Theorem decidability_reflexive : forall P : Prop,
  is_decidable P <-> (P \/ ~P).
Proof. intro P. unfold is_decidable. tauto. Qed.

Theorem classicalLogicConsistency : forall P : Prop, P \/ ~P.
Proof. apply classic. Qed.

Theorem decidability_implies_answer :
  is_decidable PEqualsNP -> (PEqualsNP \/ PNotEqualsNP).
Proof. exact (fun h => h). Qed.

Theorem double_negation :
  ~~(PEqualsNP \/ PNotEqualsNP) -> (PEqualsNP \/ PNotEqualsNP).
Proof. apply NNPP. Qed.

Print Assumptions pSubsetNP.
