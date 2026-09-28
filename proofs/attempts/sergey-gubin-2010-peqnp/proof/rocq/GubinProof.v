(* Specification of the correspondence required by Gubin's proposed LP.
   The earlier file asserted asymmetry and tour/vertex correspondence for
   placeholder definitions, then admitted the P = NP implication. Those
   assertions have been withdrawn. No instance of this specification is
   claimed for Gubin's paper. *)

Module GubinAttempt.

Record Candidate (Graph Tour Point : Type) := {
  feasible : Graph -> Point -> Prop;
  vertex : Graph -> Point -> Prop;
  integral : Point -> Prop;
  encode : Graph -> Tour -> Point;
  validTour : Graph -> Tour -> Prop
}.

Definition HasCorrespondence {Graph Tour Point : Type}
    (c : Candidate Graph Tour Point) : Prop :=
  (forall g t, validTour _ _ _ c g t ->
    feasible _ _ _ c g (encode _ _ _ c g t) /\
    vertex _ _ _ c g (encode _ _ _ c g t) /\
    integral _ _ _ c (encode _ _ _ c g t)) /\
  (forall g p, feasible _ _ _ c g p -> vertex _ _ _ c g p ->
    integral _ _ _ c p ->
    exists t, validTour _ _ _ c g t /\ encode _ _ _ c g t = p).

End GubinAttempt.
