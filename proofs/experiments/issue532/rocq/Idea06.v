(* Issue #532: 06_local_minimum. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition cost (n : nat) : nat := match n with 0 => 1 | 1 => 2 | _ => 0 end.
Theorem tested : cost 0 < cost 1 /\ cost 2 < cost 0. Proof. compute; lia. Qed.
