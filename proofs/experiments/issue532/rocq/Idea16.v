(* Issue #532: 16_finite_diagonal. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition first (_ : bool) : bool := false.
Definition second (_ : bool) : bool := true.
Definition diagonal (x : bool) : bool := negb x.
Theorem tested : diagonal false <> first false /\ diagonal true <> second true.
Proof. split; discriminate. Qed.
