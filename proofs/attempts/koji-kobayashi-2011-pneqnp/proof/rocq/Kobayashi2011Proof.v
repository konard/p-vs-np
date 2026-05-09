(*
  Forward formalization of Koji Kobayashi's 2011 proof attempt.

  The unsupported lower-bound steps are represented as axioms so the final
  chaining argument can be checked separately from the actual gaps.
*)

Require Import Coq.Strings.String.

Module Kobayashi2011ProofAttempt.

Definition Language := string -> Prop.

Record ComplexityClass := {
  contains : Language -> Prop
}.

Definition InClass (C : ComplexityClass) (L : Language) : Prop :=
  contains C L.

Definition StrictContains (A B : ComplexityClass) : Prop :=
  (forall X, InClass B X -> InClass A X) /\
  exists W, InClass A W /\ ~ InClass B W.

Parameter NP AL P NC NL L : ComplexityClass.

Axiom AL_eq_P : forall X, InClass AL X <-> InClass P X.
Axiom P_subset_NP : forall X, InClass P X -> InClass NP X.
Axiom NC_subset_P : forall X, InClass NC X -> InClass P X.
Axiom NL_subset_NC : forall X, InClass NL X -> InClass NC X.
Axiom L_subset_NL : forall X, InClass L X -> InClass NL X.

Parameter CHAOS ORDER LAYER TWINE : Language.

(* Critical unsupported lower-bound claims from the paper. *)
Axiom chaos_in_np : InClass NP CHAOS.
Axiom chaos_not_in_al : ~ InClass AL CHAOS.

Axiom order_in_p : InClass P ORDER.
Axiom order_not_in_nc : ~ InClass NC ORDER.

Axiom layer_in_nc : InClass NC LAYER.
Axiom layer_not_in_nl : ~ InClass NL LAYER.

Axiom twine_in_nl : InClass NL TWINE.
Axiom twine_not_in_l : ~ InClass L TWINE.

Theorem kobayashi_claim_np_strictly_contains_al :
  StrictContains NP AL.
Proof.
  split.
  - intros X H.
    apply P_subset_NP.
    apply AL_eq_P.
    exact H.
  - exists CHAOS. split; [exact chaos_in_np | exact chaos_not_in_al].
Qed.

Theorem kobayashi_claim_p_strictly_contains_nc :
  StrictContains P NC.
Proof.
  split.
  - intros X H. exact (NC_subset_P X H).
  - exists ORDER. split; [exact order_in_p | exact order_not_in_nc].
Qed.

Theorem kobayashi_claim_nc_strictly_contains_nl :
  StrictContains NC NL.
Proof.
  split.
  - intros X H. exact (NL_subset_NC X H).
  - exists LAYER. split; [exact layer_in_nc | exact layer_not_in_nl].
Qed.

Theorem kobayashi_claim_nl_strictly_contains_l :
  StrictContains NL L.
Proof.
  split.
  - intros X H. exact (L_subset_NL X H).
  - exists TWINE. split; [exact twine_in_nl | exact twine_not_in_l].
Qed.

Theorem kobayashi_claim_chain :
  StrictContains NP AL /\
  StrictContains P NC /\
  StrictContains NC NL /\
  StrictContains NL L.
Proof.
  split.
  - exact kobayashi_claim_np_strictly_contains_al.
  - split.
    + exact kobayashi_claim_p_strictly_contains_nc.
    + split.
      * exact kobayashi_claim_nc_strictly_contains_nl.
      * exact kobayashi_claim_nl_strictly_contains_l.
Qed.

End Kobayashi2011ProofAttempt.
