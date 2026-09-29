(*
  Feinstein2006Proof.v

  Rocq formalization of the claimed structure of Craig Alan Feinstein's 2006
  "A New and Elegant Argument that P is not NP".

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

Definition exponential_witness_space (n : nat) : nat := 2 ^ n.

Parameter feinstein_problem : DecisionProblem.

Axiom exponentially_many_candidates :
  forall n, n <= exponential_witness_space n.

(*
  The crucial claimed lower-bound premise. The refutation files isolate why
  the counting argument does not establish this statement.
*)
Axiom polynomial_algorithms_miss_candidates :
  forall alg : Algorithm,
    polynomial_time alg ->
    ~ solves alg feinstein_problem.

Theorem no_polynomial_algorithm_for_feinstein_problem :
  forall alg : Algorithm,
    polynomial_time alg ->
    ~ solves alg feinstein_problem.
Proof.
  intros alg Hpoly.
  exact (polynomial_algorithms_miss_candidates alg Hpoly).
Qed.

Parameter P_neq_NP : Prop.

Axiom np_complete_lower_bound_implies_pneqnp :
  (forall alg : Algorithm,
      polynomial_time alg ->
      ~ solves alg feinstein_problem) ->
  P_neq_NP.

Theorem feinstein_2006_conclusion : P_neq_NP.
Proof.
  apply np_complete_lower_bound_implies_pneqnp.
  exact no_polynomial_algorithm_for_feinstein_problem.
Qed.

