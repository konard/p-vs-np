(* Issue #532: 02_failed_certificate. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition sat (x y : bool) : bool := andb x (negb y).
Definition search : bool := orb (sat false false) (orb (sat false true) (orb (sat true false) (sat true true))).
Theorem tested : sat true true = false /\ search = true. Proof. split; reflexivity. Qed.
