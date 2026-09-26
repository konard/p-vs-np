(* Issue #532: 08_finite_samples. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition f (x : bool) : bool := x.
Definition g (_ : bool) : bool := false.
Theorem tested : f false = g false /\ f true <> g true.
Proof. split; [reflexivity | discriminate]. Qed.
