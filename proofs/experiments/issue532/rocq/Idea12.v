(* Issue #532: 12_reduction_soundness. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition source (x : bool) : bool := x.
Definition target (x : bool) : bool := x.
Definition badMap (_ : bool) : bool := true.
Theorem tested : source false <> target (badMap false). Proof. discriminate. Qed.
