(* Issue #532: 19_answer_as_advice. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition advice (x : bool) : bool := x.
Definition solver (_x hint : bool) : bool := hint.
Theorem tested : forall x : bool, solver x (advice x) = x.
Proof. destruct x; reflexivity. Qed.
