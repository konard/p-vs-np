(*
  Refutation notes for Jerrald Meek (2008), "Analysis of the postulates
  produced by Karp's Theorem".
*)

Module MeekKarpPostulatesRefutation.

Parameter Language : Type.
Parameter PolynomialTimeDecidable : Language -> Prop.
Parameter PolynomialTimeManyOneReducible : Language -> Language -> Prop.
Parameter IsSpecialCaseOf : Language -> Language -> Prop.
Parameter NPComplete : Language -> Prop.

Parameter SAT : Language.

Parameter sat_reduces_to_npcomplete :
  forall L : Language, NPComplete L -> PolynomialTimeManyOneReducible SAT L.

Parameter reduction_composition :
  forall A B : Language,
    PolynomialTimeManyOneReducible A B ->
    PolynomialTimeDecidable B ->
    PolynomialTimeDecidable A.

Theorem npcomplete_in_p_implies_sat_in_p :
  forall L : Language,
    NPComplete L ->
    PolynomialTimeDecidable L ->
    PolynomialTimeDecidable SAT.
Proof.
  intros L Hcomplete Hdecidable.
  exact (reduction_composition SAT L
           (sat_reduces_to_npcomplete L Hcomplete)
           Hdecidable).
Qed.

(*
  This proposition is the invalid special-case inference used in the paper.
  It is intentionally a definition, not an axiom or theorem.
*)
Definition InvalidSpecialCaseInference : Prop :=
  forall A B : Language, IsSpecialCaseOf A B -> NPComplete B -> NPComplete A.

(*
  Standard complexity theory permits easy restrictions of hard problems.
*)
Definition EasySpecialCaseOfHardProblemCanExist : Prop :=
  exists A B : Language,
    IsSpecialCaseOf A B /\
    NPComplete B /\
    PolynomialTimeDecidable A.

End MeekKarpPostulatesRefutation.
