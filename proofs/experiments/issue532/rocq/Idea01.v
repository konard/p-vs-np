(* Issue #532: 01_bounded_sat. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition sat (x y : bool) : bool := andb x (negb y).
Definition search : bool := orb (sat false false) (orb (sat false true) (orb (sat true false) (sat true true))).
Theorem tested : search = true. Proof. reflexivity. Qed.
