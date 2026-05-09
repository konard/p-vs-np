/-
  Refutation notes for Jerrald Meek (2008), "Analysis of the postulates
  produced by Karp's Theorem".
-/

namespace MeekKarpPostulatesRefutation

axiom Language : Type
axiom PolynomialTimeDecidable : Language -> Prop
axiom PolynomialTimeManyOneReducible : Language -> Language -> Prop
axiom IsSpecialCaseOf : Language -> Language -> Prop
axiom NPComplete : Language -> Prop

axiom SAT : Language

/-- SAT reduces to every NP-complete language. -/
axiom sat_reduces_to_npcomplete :
  forall L : Language, NPComplete L -> PolynomialTimeManyOneReducible SAT L

/-- Polynomial-time deciders compose with polynomial-time many-one reductions. -/
axiom reduction_composition :
  forall A B : Language,
    PolynomialTimeManyOneReducible A B ->
    PolynomialTimeDecidable B ->
    PolynomialTimeDecidable A

theorem npcomplete_in_p_implies_sat_in_p
    (L : Language)
    (hComplete : NPComplete L)
    (hDecidable : PolynomialTimeDecidable L) :
    PolynomialTimeDecidable SAT := by
  exact reduction_composition SAT L (sat_reduces_to_npcomplete L hComplete) hDecidable

/--
  This proposition is the invalid special-case inference used in the paper.
  It is intentionally a definition, not an axiom or theorem.
-/
def InvalidSpecialCaseInference : Prop :=
  forall A B : Language, IsSpecialCaseOf A B -> NPComplete B -> NPComplete A

/--
  Standard complexity theory does not license `InvalidSpecialCaseInference`.
  Easy restrictions of hard problems can be polynomial-time decidable.
-/
def EasySpecialCaseOfHardProblemCanExist : Prop :=
  exists A B : Language,
    IsSpecialCaseOf A B /\
    NPComplete B /\
    PolynomialTimeDecidable A

end MeekKarpPostulatesRefutation
