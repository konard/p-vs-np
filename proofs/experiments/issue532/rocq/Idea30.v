(* Issue #532: 30_lower_bound_transfer. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (Algorithm Circuit : Type) (compile : Algorithm -> Circuit)
  (fast : Algorithm -> Prop) (correct expensive : Circuit -> Prop) :
  (forall c, correct c -> expensive c) ->
  (forall a, fast a -> correct (compile a)) ->
  (forall a, fast a -> ~ expensive (compile a)) ->
  forall a, ~ fast a.
Proof.
  intros Hlower Hsimulation Hsize a Hfast.
  apply (Hsize a Hfast).
  apply Hlower, Hsimulation, Hfast.
Qed.
