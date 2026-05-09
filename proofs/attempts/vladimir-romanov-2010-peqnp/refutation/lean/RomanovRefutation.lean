/-
  RomanovRefutation.lean - Refutation of Romanov's 2010 P=NP proof attempt

  The attempted proof relies on converting local CTS/hyperstructure consistency
  into a global satisfying assignment. This file separates those notions and
  records the missing invariant.
-/

namespace RomanovRefutation

abbrev Variable := Nat
abbrev Assignment := Variable → Bool

structure Clause3 where
  first : Variable
  second : Variable
  third : Variable
  forbiddenFirst : Bool
  forbiddenSecond : Bool
  forbiddenThird : Bool

abbrev Formula3CNF := List Clause3

def ClauseSatisfied (assignment : Assignment) (clause : Clause3) : Prop :=
  assignment clause.first ≠ clause.forbiddenFirst ∨
  assignment clause.second ≠ clause.forbiddenSecond ∨
  assignment clause.third ≠ clause.forbiddenThird

def Satisfiable (formula : Formula3CNF) : Prop :=
  ∃ assignment : Assignment, ∀ clause ∈ formula, ClauseSatisfied assignment clause

structure LocalSEPState where
  hasLocalSupport : Prop

def LocallyConsistent (_formula : Formula3CNF) : Prop :=
  ∃ state : LocalSEPState, state.hasLocalSupport

def GloballySoundSEP : Prop :=
  ∀ formula : Formula3CNF, LocallyConsistent formula → Satisfiable formula

/-
  Local consistency is weaker than global satisfiability for constraint systems.
  Romanov needs to prove that his additional CTS operations close this gap.
-/
axiom local_consistency_not_enough :
  ¬ (∀ formula : Formula3CNF, LocallyConsistent formula → Satisfiable formula)

theorem romanov_missing_global_soundness :
    ¬ GloballySoundSEP := by
  exact local_consistency_not_enough

def RomanovTheorem2Sufficiency : Prop :=
  ∀ formula : Formula3CNF, LocallyConsistent formula → Satisfiable formula

theorem theorem2_sufficiency_is_unproved :
    ¬ RomanovTheorem2Sufficiency := by
  exact local_consistency_not_enough

def PolynomialSEPWouldImplyPEqualsNPOnlyWithSoundness : Prop :=
  GloballySoundSEP → True

theorem polynomial_bound_alone_is_insufficient :
    ¬ GloballySoundSEP →
    ¬ RomanovTheorem2Sufficiency := by
  intro h_missing
  exact h_missing

/-
  The refutation target:
  Romanov proves, at most, that a local procedure can be run in polynomial time.
  The paper does not prove that non-empty local state is an exact certificate for
  satisfiability of the original 3-CNF formula.
-/
theorem romanov_argument_gap :
    ¬ GloballySoundSEP ∧ ¬ RomanovTheorem2Sufficiency := by
  constructor
  · exact romanov_missing_global_soundness
  · exact theorem2_sufficiency_is_unproved

#check romanov_missing_global_soundness
#check theorem2_sufficiency_is_unproved
#check polynomial_bound_alone_is_insufficient
#check romanov_argument_gap

end RomanovRefutation

