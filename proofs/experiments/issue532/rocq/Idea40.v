(* Issue #532: 40_size_induction. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P : nat -> Prop) :
  P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros Hbase Hstep n; induction n.
  - exact Hbase.
  - apply Hstep, IHn.
Qed.
