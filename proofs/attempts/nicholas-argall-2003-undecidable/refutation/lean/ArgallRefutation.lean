/-
  Refutation of Nicholas Argall's 2003 undecidability claim.

  The key point is structural: incompleteness of a theory says that some
  sentence is undecidable, not that every expressible sentence is undecidable.
-/

namespace ArgallRefutation

structure Theory where
  Sentence : Type
  proves : Sentence -> Prop
  refutes : Sentence -> Prop
  expressible : Sentence -> Prop
  complete : Prop
  consistent : Prop

def IndependentOf (T : Theory) (phi : T.Sentence) : Prop :=
  Not (T.proves phi) /\ Not (T.refutes phi)

def Incomplete (T : Theory) : Prop :=
  Not T.complete

-- Argall's invalid bridge, stated as a property so it can be refuted.
def IncompletenessMakesEveryExpressibleSentenceIndependent (T : Theory) : Prop :=
  forall phi : T.Sentence,
    T.expressible phi -> T.consistent -> Incomplete T -> IndependentOf T phi

inductive TwoSentences where
  | p_eq_np
  | goedel_sentence

def counterTheory : Theory where
  Sentence := TwoSentences
  proves := fun phi =>
    match phi with
    | TwoSentences.p_eq_np => True
    | TwoSentences.goedel_sentence => False
  refutes := fun _ => False
  expressible := fun _ => True
  complete := False
  consistent := True

theorem counterTheory_is_consistent : counterTheory.consistent := by
  trivial

theorem counterTheory_is_incomplete : Incomplete counterTheory := by
  intro h
  exact h

theorem p_eq_np_is_expressible_in_counterTheory :
    counterTheory.expressible TwoSentences.p_eq_np := by
  trivial

theorem p_eq_np_is_not_independent_in_counterTheory :
    Not (IndependentOf counterTheory TwoSentences.p_eq_np) := by
  intro h
  exact h.left True.intro

theorem argall_bridge_is_false :
    Not (IncompletenessMakesEveryExpressibleSentenceIndependent counterTheory) := by
  intro bridge
  have hind := bridge TwoSentences.p_eq_np
    p_eq_np_is_expressible_in_counterTheory
    counterTheory_is_consistent
    counterTheory_is_incomplete
  exact p_eq_np_is_not_independent_in_counterTheory hind

-- The valid consequence of incompleteness is only existential.
def HasSomeIndependentSentence (T : Theory) : Prop :=
  exists phi : T.Sentence, IndependentOf T phi

theorem existential_is_weaker_than_argall_bridge :
    IncompletenessMakesEveryExpressibleSentenceIndependent counterTheory ->
    HasSomeIndependentSentence counterTheory := by
  intro bridge
  exact Exists.intro TwoSentences.goedel_sentence
    (bridge TwoSentences.goedel_sentence (by trivial)
      counterTheory_is_consistent counterTheory_is_incomplete)

end ArgallRefutation
