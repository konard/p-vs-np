(* Issue #532: 39_proof_system_scope. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  exists weak strong : bool -> Prop,
    (forall proof, weak proof -> strong proof) /\
    (forall proof, ~ weak proof) /\ (exists proof, strong proof).
Proof.
  exists (fun _ => False), (fun _ => True); split; [| split].
  - intros _ H; contradiction.
  - intros _ H; contradiction.
  - exists false; exact I.
Qed.
