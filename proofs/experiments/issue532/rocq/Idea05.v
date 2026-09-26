(* Issue #532: 05_greedy_choice. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition greedyCost : nat := 1 + 10.
Definition alternativeCost : nat := 2 + 1.
Theorem tested : alternativeCost < greedyCost. Proof. compute; lia. Qed.
