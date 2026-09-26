(* Issue #532: 36_exact_rounding. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (Discrete Relaxed : Type)
  (feasible : Discrete -> Prop) (relaxed : Relaxed -> Prop)
  (round : Relaxed -> Discrete) :
  (forall y, relaxed y -> feasible (round y)) ->
  (exists y, relaxed y) -> exists x, feasible x.
Proof.
  intros Hround [y Hy]; exists (round y); apply Hround, Hy.
Qed.
