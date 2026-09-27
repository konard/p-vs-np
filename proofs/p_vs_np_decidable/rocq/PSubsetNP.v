(** P ⊆ NP for finite machines and bounded runs. *)
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Theorem pSubsetNP : forall p : ClassP, exists np : ClassNP,
  forall x : Word, p_language p x = np_language np x.
Proof.
  intro p.
  exists (pToNP p).
  intro x. reflexivity.
Qed.

Print Assumptions pSubsetNP.
