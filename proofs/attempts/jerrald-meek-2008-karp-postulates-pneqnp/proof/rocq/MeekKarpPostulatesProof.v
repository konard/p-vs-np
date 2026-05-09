(*
  Jerrald Meek (2008), Woeginger entry #46.

  The proposed forward proof requires a gap that is incompatible with standard
  polynomial-time many-one reduction composition.
*)

Module MeekKarpPostulatesProof.

Parameter Language : Type.
Parameter PolynomialTimeDecidable : Language -> Prop.
Parameter PolynomialTimeManyOneReducible : Language -> Language -> Prop.

Parameter SAT : Language.

Parameter reduction_composition :
  forall L : Language,
    PolynomialTimeManyOneReducible SAT L ->
    PolynomialTimeDecidable L ->
    PolynomialTimeDecidable SAT.

Definition MeekRequiredGap : Prop :=
  exists L : Language,
    PolynomialTimeManyOneReducible SAT L /\
    PolynomialTimeDecidable L /\
    ~ PolynomialTimeDecidable SAT.

Theorem meek_required_gap_contradicts_reduction_composition :
  ~ MeekRequiredGap.
Proof.
  intros [L [Hreduce [Hdecide Hnot_sat]]].
  apply Hnot_sat.
  exact (reduction_composition L Hreduce Hdecide).
Qed.

End MeekKarpPostulatesProof.
