(* Issue #532: 17_enumeration_cost. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition assignments : list (bool * bool) := (false, false) :: (false, true) :: (true, false) :: (true, true) :: nil.
Theorem tested : length assignments = 4. Proof. reflexivity. Qed.
