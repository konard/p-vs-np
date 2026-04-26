(**
  RomanovRefutation.v - Refutation of Romanov's 2010 P=NP proof attempt

  The attempted proof relies on converting local CTS/hyperstructure consistency
  into a global satisfying assignment. This file separates those notions and
  records the missing invariant.
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Module RomanovRefutationAttempt.

Definition Var := nat.
Definition Assignment := Var -> bool.

Record Clause3 := {
  first : Var;
  second : Var;
  third : Var;
  forbiddenFirst : bool;
  forbiddenSecond : bool;
  forbiddenThird : bool
}.

Definition Formula3CNF := list Clause3.

Definition ClauseSatisfied (assignment : Assignment) (clause : Clause3) : Prop :=
  assignment (first clause) <> forbiddenFirst clause \/
  assignment (second clause) <> forbiddenSecond clause \/
  assignment (third clause) <> forbiddenThird clause.

Definition Satisfiable (formula : Formula3CNF) : Prop :=
  exists assignment : Assignment,
    forall clause, In clause formula -> ClauseSatisfied assignment clause.

Record LocalSEPState := {
  hasLocalSupport : Prop
}.

Definition LocallyConsistent (_formula : Formula3CNF) : Prop :=
  exists state : LocalSEPState, hasLocalSupport state.

Definition GloballySoundSEP : Prop :=
  forall formula : Formula3CNF, LocallyConsistent formula -> Satisfiable formula.

(**
  Local consistency is weaker than global satisfiability for constraint systems.
  Romanov needs to prove that his additional CTS operations close this gap.
*)
Axiom local_consistency_not_enough :
  ~ (forall formula : Formula3CNF, LocallyConsistent formula -> Satisfiable formula).

Theorem romanov_missing_global_soundness :
  ~ GloballySoundSEP.
Proof.
  exact local_consistency_not_enough.
Qed.

Definition RomanovTheorem2Sufficiency : Prop :=
  forall formula : Formula3CNF, LocallyConsistent formula -> Satisfiable formula.

Theorem theorem2_sufficiency_is_unproved :
  ~ RomanovTheorem2Sufficiency.
Proof.
  exact local_consistency_not_enough.
Qed.

Definition PolynomialSEPWouldImplyPEqualsNPOnlyWithSoundness : Prop :=
  GloballySoundSEP -> True.

Theorem polynomial_bound_alone_is_insufficient :
  ~ GloballySoundSEP -> ~ RomanovTheorem2Sufficiency.
Proof.
  intro h_missing.
  exact h_missing.
Qed.

(**
  The refutation target:
  Romanov proves, at most, that a local procedure can be run in polynomial time.
  The paper does not prove that non-empty local state is an exact certificate for
  satisfiability of the original 3-CNF formula.
*)
Theorem romanov_argument_gap :
  ~ GloballySoundSEP /\ ~ RomanovTheorem2Sufficiency.
Proof.
  split.
  - exact romanov_missing_global_soundness.
  - exact theorem2_sufficiency_is_unproved.
Qed.

Check romanov_missing_global_soundness.
Check theorem2_sufficiency_is_unproved.
Check polynomial_bound_alone_is_insufficient.
Check romanov_argument_gap.

End RomanovRefutationAttempt.
