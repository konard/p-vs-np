(* Issue #532: 23_resolution_soundness. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P R S : Prop) :
  P \/ R -> ~ P \/ S -> R \/ S.
Proof.
  intros [HP | HR] [HNP | HS]; try tauto.
Qed.
