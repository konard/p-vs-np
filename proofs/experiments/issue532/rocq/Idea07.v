(* Issue #532: 07_lossy_compression. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Definition encode (p : bool * bool) : bool := fst p.
Theorem tested : encode (false, false) = encode (false, true) /\ (false, false) <> (false, true).
Proof. split; [reflexivity | discriminate]. Qed.
