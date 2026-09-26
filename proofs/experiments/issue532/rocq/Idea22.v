(* Issue #532: 22_decision_guides_search. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P Q : Prop) (b : bool) :
  (b = true <-> P) -> P \/ Q -> if b then P else Q.
Proof.
  intros Horacle Hexists; destruct b.
  - apply Horacle; reflexivity.
  - destruct Hexists as [HP | HQ].
    + apply Horacle in HP; discriminate.
    + exact HQ.
Qed.
