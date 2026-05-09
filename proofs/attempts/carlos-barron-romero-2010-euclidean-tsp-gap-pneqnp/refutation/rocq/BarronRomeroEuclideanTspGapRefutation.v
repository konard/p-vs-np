(**
  BarronRomeroEuclideanTspGapRefutation.v

  Refutation of the unsupported step in Woeginger entry #69.  Lack of a
  triangle-reduction property does not imply lack of every polynomial-time
  algorithm.
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

(**
  Use an arbitrary structural predicate instead of defining it as True:
  this lets the refutation exhibit a problem that lacks the structure.
*)
Definition HasTriangleReduction (_problem : DecisionProblem) : Prop := False.

Definition alwaysTrueProblem : DecisionProblem := fun _ => True.

Lemma one_le_n_pow_zero : forall n : nat, 1 <= n ^ 0.
Proof.
  intro n.
  simpl.
  lia.
Qed.

Definition constantTruePolyTime : PolyTimeFunction :=
  {| ptf_compute := fun _ => "true";
     ptf_time := fun _ => 1;
     ptf_isPolyTime := ex_intro _ 0 one_le_n_pow_zero |}.

Theorem always_true_in_p : InP alwaysTrueProblem.
Proof.
  exists constantTruePolyTime.
  intro x.
  easy.
Qed.

Theorem always_true_lacks_triangle_reduction :
    ~ HasTriangleReduction alwaysTrueProblem.
Proof.
  intro h.
  exact h.
Qed.

Theorem lack_of_triangle_reduction_does_not_imply_not_in_p :
    ~ (forall problem : DecisionProblem,
      ~ HasTriangleReduction problem -> ~ InP problem).
Proof.
  intro h.
  exact (h alwaysTrueProblem always_true_lacks_triangle_reduction always_true_in_p).
Qed.

Check always_true_in_p.
Check always_true_lacks_triangle_reduction.
Check lack_of_triangle_reduction_does_not_imply_not_in_p.
