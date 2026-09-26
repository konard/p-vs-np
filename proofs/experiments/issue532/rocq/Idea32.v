(* Issue #532: 32_promise_coverage. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  exists promise answer : bool -> bool,
    (forall x, promise x = true -> answer x = x) /\ answer false <> false.
Proof.
  exists (fun x => x), (fun _ => true); split.
  - intros [] H; simpl in *; [reflexivity | discriminate].
  - discriminate.
Qed.
