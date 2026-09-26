(* Issue #532: 14_random_seed. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition randomizedAnswer (seed : bool) : bool := seed.
Theorem tested : randomizedAnswer true = true /\ randomizedAnswer false = false.
Proof. split; reflexivity. Qed.
