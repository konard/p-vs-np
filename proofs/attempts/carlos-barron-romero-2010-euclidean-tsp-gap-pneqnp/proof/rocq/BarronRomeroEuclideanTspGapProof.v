(**
  BarronRomeroEuclideanTspGapProof.v

  Formal sketch of Carlos Barron-Romero's Woeginger entry #69 attempt:
  "The Complexity of Euclidian 2 Dimension Travelling Salesman Problem
  versus General Assign Problem, NP is not P" (arXiv:1101.0160).
*)

From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import Lia.
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

(** The paper's geometric reduction property for Euclidean 2D TSP. *)
Definition HasTriangleReduction (_problem : DecisionProblem) : Prop := True.

(** Abstract representatives of the paper's two classes. *)
Axiom e2dtsp : DecisionProblem.
Axiom gap : DecisionProblem.

Axiom e2dtsp_in_np : InNP e2dtsp.
Axiom e2dtsp_triangle_reducible : HasTriangleReduction e2dtsp.

Axiom gap_in_np : InNP gap.

(**
  The paper's structural claim: arbitrary GAP instances need not preserve
  the triangle-reduction property used for E2DTSP.
*)
Axiom gap_lacks_triangle_reduction : ~ HasTriangleReduction gap.

(**
  CLAIMED CRITICAL STEP:

  The paper needs this implication to move from a missing geometric
  property to a lower bound against every polynomial-time algorithm.
*)
Theorem no_triangle_reduction_implies_not_in_p :
    ~ HasTriangleReduction gap -> ~ InP gap.
Admitted. (* PROOF FAILS HERE: no universal lower bound is supplied. *)

Theorem gap_not_in_p : ~ InP gap.
Proof.
  exact (no_triangle_reduction_implies_not_in_p gap_lacks_triangle_reduction).
Qed.

Theorem barron_romero_2010_claim :
    ~ (forall problem, InP problem <-> InNP problem).
Proof.
  intro h_eq.
  apply gap_not_in_p.
  exact (proj2 (h_eq gap) gap_in_np).
Qed.

Check e2dtsp_triangle_reducible.
Check gap_lacks_triangle_reduction.
Check no_triangle_reduction_implies_not_in_p.
Check barron_romero_2010_claim.
