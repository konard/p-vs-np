(* Issue #532: 11_relaxation_gap. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition cost (n : nat) : nat := if Nat.eqb n 1 then 0 else 1.
Theorem tested : cost 1 < cost 0 /\ cost 1 < cost 2.
Proof. compute; lia. Qed.
