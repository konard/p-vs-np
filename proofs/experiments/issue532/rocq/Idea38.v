(* Issue #532: 38_oracle_worlds. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  exists property : bool -> Prop, property false /\ ~ property true.
Proof.
  exists (fun oracle => oracle = false); split; [reflexivity | discriminate].
Qed.
