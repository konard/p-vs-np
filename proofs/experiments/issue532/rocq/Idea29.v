(* Issue #532: 29_reduction_correctness_chain. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (X Y : Type) (A : X -> Prop) (B D : Y -> Prop)
  (reduce : X -> Y) :
  (forall x, A x <-> B (reduce x)) ->
  (forall y, B y <-> D y) -> forall x, A x <-> D (reduce x).
Proof.
  intros Hreduce Hdecide x; transitivity (B (reduce x)).
  - apply Hreduce.
  - apply Hdecide.
Qed.
