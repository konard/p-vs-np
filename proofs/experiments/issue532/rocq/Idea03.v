(* Issue #532: 03_verifier_soundness. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition verify (x y : bool) : bool := andb x y.
Theorem tested : forall x y : bool, verify x y = true -> x = true /\ y = true.
Proof. destruct x, y; simpl; intros H; try discriminate; split; reflexivity. Qed.
