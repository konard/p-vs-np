(* Issue #532: 26_separator_agreement. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  (exists b : bool, b = true) /\ (exists b : bool, b = false) /\
  ~ (exists b : bool, b = true /\ b = false).
Proof.
  split; [exists true; reflexivity | split].
  - exists false; reflexivity.
  - intros [b [HT HF]]; rewrite HT in HF; discriminate.
Qed.
