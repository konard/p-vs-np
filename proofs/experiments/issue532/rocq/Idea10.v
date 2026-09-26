(* Issue #532: 10_monotone_boundary. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition negation (x : bool) : bool := negb x.
Theorem tested : negation false = true /\ negation true = false.
Proof. split; reflexivity. Qed.
