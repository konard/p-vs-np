(* Issue #532: 28_definitional_extension. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P : Prop) :
  (exists z : Prop, (z <-> P) /\ z) <-> P.
Proof.
  split.
  - intros [z [Hz Htrue]]; apply Hz; exact Htrue.
  - intro HP; exists P; split; [tauto | exact HP].
Qed.
