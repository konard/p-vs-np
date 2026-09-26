(* Issue #532: 15_size_vs_depth. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Inductive shape := chain | balanced.
Definition size (s : shape) : nat := match s with chain => 3 | balanced => 3 end.
Definition depth (s : shape) : nat := match s with chain => 3 | balanced => 2 end.
Theorem tested : size chain = size balanced /\ depth chain <> depth balanced.
Proof. split; [reflexivity | discriminate]. Qed.
