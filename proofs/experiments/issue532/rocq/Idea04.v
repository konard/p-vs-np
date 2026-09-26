(* Issue #532: 04_pairwise_consistency. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition allConstraints (x y z : bool) : bool := andb (andb (xorb x y) (xorb y z)) (xorb x z).
Theorem tested : forall x y z : bool, allConstraints x y z = false.
Proof. destruct x, y, z; reflexivity. Qed.
