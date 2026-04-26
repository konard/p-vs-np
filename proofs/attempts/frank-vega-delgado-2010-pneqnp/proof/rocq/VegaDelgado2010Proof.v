(**
  VegaDelgado2010Proof.v - Formalization of Vega Delgado's November 2010 P≠NP proof attempt

  This file formalizes the CERTIFYING argument from the 2010 paper
  "A Solution to the P versus NP Problem" (Woeginger entry #68).

  The paper claims that a CERTIFYING problem lies in NP and that if it were
  in P then some undecidable language would be forced into NP.
  The missing implication is the critical gap.
*)

From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical_Prop.
Import ListNotations.
Open Scope string_scope.

(** * Basic Types *)

Definition DecisionProblem := string -> Prop.
Definition TimeComplexity := nat -> nat.

Definition IsPolynomialTime (f : TimeComplexity) : Prop :=
  exists k : nat, forall n : nat, f n <= n ^ k.

(** A function computable in polynomial time *)
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

(** The paper's CERTIFYING problem is kept abstract at the language level. *)
Axiom certifyingProblem : DecisionProblem.
Axiom certifying_in_np : InNP certifyingProblem.

(** Standard computability fact: NP languages are decidable. *)
Axiom np_languages_are_decidable : forall problem, InNP problem -> Decidable problem.

(**
  CLAIMED CRITICAL STEP:

  Vega Delgado argues that if CERTIFYING were in P, then some undecidable language
  would belong to NP.  This is the unsupported step.
*)
Theorem certifying_in_p_implies_undecidable_np :
    InP certifyingProblem -> exists (bad : DecisionProblem), Undecidable bad /\ InNP bad.
Admitted. (* PROOF FAILS HERE — missing reduction from CERTIFYING to undecidable NP *)

Theorem certifying_not_in_p : ~ InP certifyingProblem.
Proof.
  intro h_p.
  destruct (certifying_in_p_implies_undecidable_np h_p) as [bad [h_bad_undec h_bad_np]].
  exact (h_bad_undec (np_languages_are_decidable bad h_bad_np)).
Qed.

Theorem vega_delgado_2010_claim :
    ~ (forall problem, InP problem <-> InNP problem).
Proof.
  intro h_eq.
  apply certifying_not_in_p.
  exact (proj2 (h_eq certifyingProblem) certifying_in_np).
Qed.

(**
  SUMMARY OF THE GAP

  The paper'"'"'s intended contradiction needs:
    CERTIFYING ∈ P -> exists bad, Undecidable bad /\ InNP bad

  That implication is the unresolved part of the proof.
*)

Check certifyingProblem.
Check certifying_in_np.
Check certifying_in_p_implies_undecidable_np.
Check certifying_not_in_p.
Check vega_delgado_2010_claim.
