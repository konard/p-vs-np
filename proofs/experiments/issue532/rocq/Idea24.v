(* Issue #532: 24_unit_propagation. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (P Q : Prop) : P -> ~ P \/ Q -> Q.
Proof. intros HP [HNP | HQ]; [contradiction | exact HQ]. Qed.
