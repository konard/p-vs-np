(* Issue #532: 35_exact_compression. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested (X Code : Type) (encode : X -> Code) (decode : Code -> X) :
  (forall x, decode (encode x) = x) ->
  forall x y, encode x = encode y -> x = y.
Proof.
  intros Hround x y Hequal.
  rewrite <- (Hround x), <- (Hround y).
  now rewrite Hequal.
Qed.
