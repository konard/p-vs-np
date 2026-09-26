(* Issue #532: 18_restricted_instance. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition easy (x : bool) : bool := orb x true.
Definition general (x y : bool) : bool := orb x y.
Theorem tested : (forall x : bool, easy x = true) /\ general false false = false.
Proof. split; [destruct x; reflexivity | reflexivity]. Qed.
