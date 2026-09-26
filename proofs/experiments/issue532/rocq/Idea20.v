(* Issue #532: 20_parallel_depth. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition serial : nat := 3 + 5.
Definition independent : nat := Nat.max 3 5.
Definition dependent : nat := 3 + 5.
Theorem tested : independent < serial /\ dependent = serial.
Proof. compute; lia. Qed.
