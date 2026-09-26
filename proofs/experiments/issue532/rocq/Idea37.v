(* Issue #532: 37_parameter_bound. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (cost : nat -> nat) (k cap : nat) :
  (forall a b, a <= b -> cost a <= cost b) ->
  k <= cap -> cost k <= cost cap.
Proof. intros Hmono Hbound; apply Hmono, Hbound. Qed.
