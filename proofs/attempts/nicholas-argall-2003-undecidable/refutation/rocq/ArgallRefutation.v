(*
  Refutation of Nicholas Argall's 2003 undecidability claim.

  The key point is structural: incompleteness of a theory says that some
  sentence is undecidable, not that every expressible sentence is undecidable.
*)

Module ArgallRefutation.

Record Theory := {
  Sentence : Type;
  proves : Sentence -> Prop;
  refutes : Sentence -> Prop;
  expressible : Sentence -> Prop;
  complete : Prop;
  consistent : Prop
}.

Definition IndependentOf (T : Theory) (phi : Sentence T) : Prop :=
  ~ proves T phi /\ ~ refutes T phi.

Definition Incomplete (T : Theory) : Prop :=
  ~ complete T.

Definition IncompletenessMakesEveryExpressibleSentenceIndependent
    (T : Theory) : Prop :=
  forall phi : Sentence T,
    expressible T phi -> consistent T -> Incomplete T -> IndependentOf T phi.

Inductive TwoSentences : Type :=
  | p_eq_np
  | goedel_sentence.

Definition counterTheory : Theory :=
  {|
    Sentence := TwoSentences;
    proves := fun phi =>
      match phi with
      | p_eq_np => True
      | goedel_sentence => False
      end;
    refutes := fun _ => False;
    expressible := fun _ => True;
    complete := False;
    consistent := True
  |}.

Theorem counterTheory_is_consistent : consistent counterTheory.
Proof.
  exact I.
Qed.

Theorem counterTheory_is_incomplete : Incomplete counterTheory.
Proof.
  unfold Incomplete, counterTheory; simpl.
  intro h.
  exact h.
Qed.

Theorem p_eq_np_is_expressible_in_counterTheory :
    expressible counterTheory p_eq_np.
Proof.
  exact I.
Qed.

Theorem p_eq_np_is_not_independent_in_counterTheory :
    ~ IndependentOf counterTheory p_eq_np.
Proof.
  intro h.
  exact (proj1 h I).
Qed.

Theorem argall_bridge_is_false :
    ~ IncompletenessMakesEveryExpressibleSentenceIndependent counterTheory.
Proof.
  intro bridge.
  pose proof (bridge p_eq_np
    p_eq_np_is_expressible_in_counterTheory
    counterTheory_is_consistent
    counterTheory_is_incomplete) as hind.
  exact (p_eq_np_is_not_independent_in_counterTheory hind).
Qed.

Definition HasSomeIndependentSentence (T : Theory) : Prop :=
  exists phi : Sentence T, IndependentOf T phi.

Theorem existential_is_weaker_than_argall_bridge :
    IncompletenessMakesEveryExpressibleSentenceIndependent counterTheory ->
    HasSomeIndependentSentence counterTheory.
Proof.
  intro bridge.
  exists goedel_sentence.
  apply bridge.
  - exact I.
  - exact counterTheory_is_consistent.
  - exact counterTheory_is_incomplete.
Qed.

End ArgallRefutation.
