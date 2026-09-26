(* Issue #532: 25_independent_components. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (X Y : Type) (A : X -> Prop) (B : Y -> Prop) :
  (exists x, A x) /\ (exists y, B y) <-> exists x y, A x /\ B y.
Proof.
  split.
  - intros [[x HX] [y HY]]; exists x, y; split; assumption.
  - intros [x [y [HX HY]]]; split; [exists x | exists y]; assumption.
Qed.
