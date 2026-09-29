/-
  Jerrald Meek (2008), Woeginger entry #46.

  This file records why the proposed forward proof cannot be completed as a
  Lean theorem: it requires denying the standard composition principle for
  polynomial-time many-one reductions.
-/

namespace MeekKarpPostulatesProof

axiom Language : Type
axiom PolynomialTimeDecidable : Language -> Prop
axiom PolynomialTimeManyOneReducible : Language -> Language -> Prop

axiom SAT : Language

/-- Standard reduction composition: if SAT reduces to L and L is in P, then SAT is in P. -/
axiom reduction_composition :
  forall (L : Language),
    PolynomialTimeManyOneReducible SAT L ->
    PolynomialTimeDecidable L ->
    PolynomialTimeDecidable SAT

/-- Meek's argument would need this standard implication to fail. -/
def MeekRequiredGap : Prop :=
  exists L : Language,
    PolynomialTimeManyOneReducible SAT L /\
    PolynomialTimeDecidable L /\
    Not (PolynomialTimeDecidable SAT)

theorem meek_required_gap_contradicts_reduction_composition :
  Not MeekRequiredGap := by
  intro h
  rcases h with ⟨L, hReduce, hDecide, hNoSAT⟩
  exact hNoSAT (reduction_composition L hReduce hDecide)

end MeekKarpPostulatesProof
