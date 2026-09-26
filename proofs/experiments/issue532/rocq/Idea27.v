(* Issue #532: 27_variable_elimination. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P Q : Prop) :
  (exists b : bool, (b = true /\ P) \/ (b = false /\ Q)) <-> P \/ Q.
Proof.
  split.
  - intros [b [[_ HP] | [_ HQ]]]; [left | right]; assumption.
  - intros [HP | HQ].
    + exists true; left; split; [reflexivity | assumption].
    + exists false; right; split; [reflexivity | assumption].
Qed.
