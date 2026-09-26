(* Issue #532: 21_branching_exhaustive. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P Q : Prop) :
  (P \/ Q) <-> exists b : bool, if b then P else Q.
Proof.
  split.
  - intros [HP | HQ]; [exists true | exists false]; assumption.
  - intros [b H]; destruct b; [left | right]; assumption.
Qed.
