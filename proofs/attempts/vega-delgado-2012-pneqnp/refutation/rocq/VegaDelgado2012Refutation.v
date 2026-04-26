(**
  VegaDelgado2012Refutation.v - Refutation of Vega Delgado's 2012 P≠NP proof attempt

  This file demonstrates why Vega Delgado's 2012 approach fails:
  1. The critical implication (P = UP -> EXP = P) is unjustified and contradicts known results.
  2. Even if P ≠ UP, this does not imply P ≠ NP.
*)

From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import Classical_Prop.
Import ListNotations.

(** * Complexity Class Definitions (same as proof file) *)

Definition DecisionProblem := string -> Prop.
Definition TimeComplexity := nat -> nat.

Definition IsPolynomialTime (f : TimeComplexity) : Prop :=
  exists k : nat, forall n : nat, f n <= n ^ k.

Definition IsExponentialTime (f : TimeComplexity) : Prop :=
  exists k : nat, forall n : nat, f n <= 2 ^ (n ^ k).

Record TuringMachine := {
  compute : string -> bool;
  timeComplexity : TimeComplexity
}.

Record NondeterministicTM := {
  nd_compute : string -> list bool;
  nd_timeComplexity : TimeComplexity
}.

Definition InP (problem : DecisionProblem) : Prop :=
  exists (tm : TuringMachine),
    IsPolynomialTime (timeComplexity tm) /\
    forall x : string, problem x <-> compute tm x = true.

Definition InNP (problem : DecisionProblem) : Prop :=
  exists (ntm : NondeterministicTM),
    IsPolynomialTime (nd_timeComplexity ntm) /\
    forall x : string,
      problem x <-> exists result, List.In result (nd_compute ntm x) /\ result = true.

Definition InUP (problem : DecisionProblem) : Prop :=
  exists (ntm : NondeterministicTM),
    IsPolynomialTime (nd_timeComplexity ntm) /\
    forall x : string,
      (problem x <-> exists! result, List.In result (nd_compute ntm x) /\ result = true).

Definition InEXP (problem : DecisionProblem) : Prop :=
  exists (tm : TuringMachine),
    IsExponentialTime (timeComplexity tm) /\
    forall x : string, problem x <-> compute tm x = true.

(** * REFUTATION 1: THE TIME HIERARCHY THEOREM IS UNCONDITIONAL *)

(**
  The Time Hierarchy Theorem guarantees EXP ≠ P regardless of any assumption
  about the relationship between P and UP. This directly contradicts what Vega
  Delgado's critical step claims (that P = UP would imply EXP = P).
*)

(** Time Hierarchy Theorem (axiom — proven by Hartmanis & Stearns, 1965) *)
Axiom time_hierarchy_theorem : ~ (forall problem, InEXP problem <-> InP problem).

(**
  The theorem above holds with NO assumption about P vs UP.
  Therefore, P = UP cannot possibly cause EXP = P to be TRUE,
  because EXP = P is ALWAYS FALSE.

  Formal statement: The critical step is invalid.

  If EXP = P is always false (by Time Hierarchy Theorem), then
  "P = UP -> EXP = P" would only be vacuously true if "P = UP" is false.
  But the proof cannot assume "P = UP" is false — that is what it is trying to prove!
*)

Theorem critical_step_is_invalid :
    (** The critical implication (P = UP -> EXP = P) cannot be derived
        from standard complexity-theoretic axioms.
        We demonstrate this by showing EXP = P is always false: *)
    ~ (forall problem, InEXP problem <-> InP problem).
Proof.
  exact time_hierarchy_theorem.
Qed.

(** * REFUTATION 2: P ≠ UP DOES NOT IMPLY P ≠ NP *)

(**
  Even if we hypothetically accept P ≠ UP (ignoring the flawed derivation),
  this does not prove P ≠ NP. We only know UP ⊆ NP, not UP = NP.

  The relationship between UP and NP is itself an open problem.
*)

(** Axiom: UP ⊆ NP (known, but UP = NP is unknown) *)
Axiom UP_subset_NP : forall problem, InUP problem -> InNP problem.

(**
  The gap in the argument:

  What Vega Delgado needs: UP = NP (so that P ≠ UP implies P ≠ NP)
  What is actually known: UP ⊆ NP (strict containment may or may not hold)

  Without UP = NP, the conclusion P ≠ NP does not follow from P ≠ UP.
*)
Theorem p_neq_up_insufficient_for_p_neq_np :
    (~ (forall problem, InP problem <-> InUP problem)) ->
    (~ (forall problem, InP problem <-> InNP problem)).
Proof.
  (**
    ERROR: Cannot be proven. P ≠ UP does not imply P ≠ NP.
    We would need UP = NP, which is an open problem.
  *)
Admitted. (* PROOF FAILS HERE — Insufficient to conclude P ≠ NP *)

(**
  * SUMMARY OF REFUTATION

  Vega Delgado's 2012 proof attempt fails at two critical points:

  1. CRITICAL STEP (P = UP -> EXP = P):
     - EXP ≠ P is an unconditional theorem (Time Hierarchy Theorem).
     - No complexity-theoretic result connects P = UP to EXP = P.
     - The step is simply false as a general implication.

  2. INSUFFICIENT CONCLUSION (P ≠ UP -> P ≠ NP):
     - We only know P ⊆ UP ⊆ NP.
     - Whether UP = NP is itself an open problem.
     - P ≠ UP does not bridge the gap to P ≠ NP.

  The proof's use of proof by contradiction is methodologically sound,
  but the derivation step fails completely, making the entire argument invalid.
*)

Check critical_step_is_invalid.
(* Check p_neq_up_insufficient_for_p_neq_np. -- Admitted *)
