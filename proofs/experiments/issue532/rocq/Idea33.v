(* Issue #532: 33_average_vs_worst. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  exists f : bool * bool -> bool,
    f (false, false) = false /\ f (false, true) = true /\
    f (true, false) = true /\ f (true, true) = true.
Proof.
  exists (fun p => orb (fst p) (snd p)); repeat split; reflexivity.
Qed.
