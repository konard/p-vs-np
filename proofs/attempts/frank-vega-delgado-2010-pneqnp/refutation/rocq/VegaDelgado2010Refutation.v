(**
  VegaDelgado2010Refutation.v - Refutation of Vega Delgado's November 2010 P≠NP proof attempt

  The paper's gap is the unsupported implication from CERTIFYING ∈ P to
  an undecidable language in NP.
*)

From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical_Prop.
Import ListNotations.
Open Scope string_scope.

Definition DecisionProblem := string -> Prop.
Definition TimeComplexity := nat -> nat.

Definition IsPolynomialTime (f : TimeComplexity) : Prop :=
  exists k : nat, forall n : nat, f n <= n ^ k.

Record PolyTimeFunction := {
  ptf_compute : string -> string;
  ptf_time : TimeComplexity;
  ptf_isPolyTime : IsPolynomialTime ptf_time
}.

Definition InP (problem : DecisionProblem) : Prop :=
  exists (f : PolyTimeFunction),
    forall (x : string), problem x <-> ptf_compute f x = "true".

Definition InNP (problem : DecisionProblem) : Prop :=
  exists (verify : PolyTimeFunction),
    forall (x : string),
      problem x <-> exists (cert : string), ptf_compute verify (x ++ cert) = "true".

Definition Decidable (problem : DecisionProblem) : Prop :=
  exists (decider : string -> bool), forall (x : string), problem x <-> decider x = true.

Definition Undecidable (problem : DecisionProblem) : Prop :=
  ~ Decidable problem.

(** The paper'"'"'s CERTIFYING problem is kept abstract at the language level. *)
Axiom certifyingProblem : DecisionProblem.
Axiom certifying_in_np : InNP certifyingProblem.
Axiom np_languages_are_decidable : forall problem, InNP problem -> Decidable problem.

(**
  The proof attempt needs this implication, but does not provide it.
  We keep it admitted in the refutation to document the exact gap.
*)
Theorem certifying_in_p_implies_undecidable_np :
    InP certifyingProblem -> exists (bad : DecisionProblem), Undecidable bad /\ InNP bad.
Admitted. (* missing reduction from CERTIFYING to undecidable NP *)

Theorem undecidable_not_in_np : forall problem, Undecidable problem -> ~ InNP problem.
Proof.
  intros problem h_undec h_np.
  exact (h_undec (np_languages_are_decidable problem h_np)).
Qed.

Theorem certifying_gap_is_the_issue :
    InP certifyingProblem -> False.
Proof.
  intro h_p.
  destruct (certifying_in_p_implies_undecidable_np h_p) as [bad [h_bad_undec h_bad_np]].
  exact (undecidable_not_in_np bad h_bad_undec h_bad_np).
Qed.

Check certifyingProblem.
Check certifying_in_np.
Check certifying_in_p_implies_undecidable_np.
Check undecidable_not_in_np.
Check certifying_gap_is_the_issue.
