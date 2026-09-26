(* Issue #532: 31_lengthwise_advice. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (f : bool -> bool) :
  exists table : bool * bool, f false = fst table /\ f true = snd table.
Proof. exists (f false, f true); split; reflexivity. Qed.
