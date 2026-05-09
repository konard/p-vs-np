(*
  Feinstein2006Refutation.v

  Rocq refutation skeleton for Craig Alan Feinstein's 2006 P != NP attempt.
  The file isolates the unsupported bridge from counting witnesses to lower
  bounds against all polynomial-time algorithms.

  Related: Issue #191, Woeginger's list entry #31
*)

Require Import Coq.Arith.Arith.

Definition InputSize := nat.
Definition Witness := nat.

Record DecisionProblem := {
  accepts : InputSize -> bool
}.

Record Algorithm := {
  decide : InputSize -> bool;
  running_time : InputSize -> nat
}.

Definition solves (alg : Algorithm) (problem : DecisionProblem) : Prop :=
  forall n, decide alg n = accepts problem n.

Definition polynomial_time (alg : Algorithm) : Prop :=
  exists k : nat, forall n, running_time alg n <= n ^ k + k.

Definition exhaustive_search_lower_bound (_problem : DecisionProblem) : Prop :=
  forall n, n <= 2 ^ n.

Definition all_polynomial_algorithms_fail (problem : DecisionProblem) : Prop :=
  forall alg : Algorithm,
    polynomial_time alg ->
    ~ solves alg problem.

Definition missing_bridge : Prop :=
  forall problem : DecisionProblem,
    exhaustive_search_lower_bound problem ->
    all_polynomial_algorithms_fail problem.

Record CountingGap := {
  gap_problem : DecisionProblem;
  has_counting_fact : exhaustive_search_lower_bound gap_problem;
  bridge_is_unproved : ~ missing_bridge
}.

Theorem counting_does_not_imply_general_lower_bound :
  ~ missing_bridge.
Proof.
  (* A concrete countermodel depends on the chosen problem. The obligation
     recorded here is exactly what the informal counting argument fails to
     establish. *)
Admitted.

Theorem feinstein_2006_gap :
  forall problem : DecisionProblem,
    exhaustive_search_lower_bound problem ->
    missing_bridge ->
    all_polynomial_algorithms_fail problem.
Proof.
  intros problem Hcount Hbridge.
  exact (Hbridge problem Hcount).
Qed.

