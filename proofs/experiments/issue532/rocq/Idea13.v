(* Issue #532: 13_approximation_gap. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition optimum : nat := 3.
Definition approximate : nat := 4.
Theorem tested : approximate <= 2 * optimum /\ approximate <> optimum.
Proof. compute; lia. Qed.
