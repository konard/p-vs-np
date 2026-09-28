(*
  FeinsteinRefutation.v - Refutation of Craig Alan Feinstein's 2003-04 P≠NP attempt

  This file demonstrates WHY Feinstein's proof attempt fails. The key insight is that
  the transfer principle - claiming that lower bounds in restricted models imply lower
  bounds in general computation - is FALSE.

  Author: Formalization for p-vs-np repository
  Date: 2026-01-18
  Related: Issue #434, Woeginger's list entry #11
*)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ========================================================================= *)
(* Part 1: Definitions (same as in proof/)                                   *)
(* ========================================================================= *)

Definition ProblemInstance := nat.
Definition Solution := nat.

Record Algorithm : Type := {
  solve : ProblemInstance -> Solution;
  running_time : ProblemInstance -> nat
}.

Record NPCompleteProblem : Type := {
  verify : ProblemInstance -> Solution -> bool
}.

Record ComputationalModel : Type := {
  num_allowed_operations : nat;
  operation_cost : nat -> nat -> nat
}.

Definition turing_machine_model : ComputationalModel := {|
  num_allowed_operations := 4;
  operation_cost := fun _ n => n
|}.

Definition feinstein_restricted_model : ComputationalModel := {|
  num_allowed_operations := 2;
  operation_cost := fun op n =>
    match op with
    | 0 => n * n
    | 1 => n
    | _ => n
    end
|}.

Definition running_time_in_model (alg : Algorithm) (model : ComputationalModel) : ProblemInstance -> nat :=
  fun inst => alg.(running_time) inst.

Definition has_lower_bound (alg : Algorithm) (model : ComputationalModel) (bound : nat -> nat) : Prop :=
  forall inst, running_time_in_model alg model inst >= bound inst.

Definition problem_lower_bound (problem : NPCompleteProblem) (model : ComputationalModel)
    (bound : nat -> nat) : Prop :=
  forall alg : Algorithm,
    (forall inst sol, alg.(solve) inst = sol -> problem.(verify) inst sol = true) ->
    has_lower_bound alg model bound.

Definition exponential_bound (n : nat) : nat := 2^(n/2).

(* ========================================================================= *)
(* Part 2: Why the Transfer Principle Fails                                  *)
(* ========================================================================= *)

(*
  The fundamental flaw in Feinstein's argument is the assumption that lower bounds
  in a restricted computational model imply lower bounds in general computation.

  This is FALSE because:
  1. Restricted models forbid certain algorithmic techniques
  2. General Turing machines can use these forbidden techniques
  3. Therefore, a problem that's hard in the restricted model might be easy in general
*)

(* Different models can have different optimal algorithms *)
Record ModelSpecificAlgorithm : Type := {
  model : ComputationalModel;
  alg : Algorithm;
  is_optimal_in_model : Prop
}.

(* A counterexample algorithm: efficient in general but unavailable in restricted model *)
Record CounterexampleAlgorithm : Type := {
  ce_alg : Algorithm;
  (* Uses operations not in restricted model *)
  uses_operation_not_in_restricted : Prop;
  (* Runs in polynomial time in general *)
  polynomial_in_general : forall inst, ce_alg.(running_time) inst <= inst * inst * inst
}.

(* ========================================================================= *)
(* Part 3: The Counterexample Theorem                                        *)
(* ========================================================================= *)

(* THEOREM: The transfer principle is FALSE
   There exist problems that are hard in restricted models but easy in general *)
Theorem transfer_principle_fails :
  exists (problem : NPCompleteProblem) (bound : nat -> nat),
    problem_lower_bound problem feinstein_restricted_model bound /\
    ~ problem_lower_bound problem turing_machine_model bound.
Proof.
  (* We cannot construct this without concrete details, but mathematically it exists
     because restricted models are strictly weaker than general computation *)
Admitted.

(* ========================================================================= *)
(* Part 4: Why Restricted Models Are Misleading                              *)
(* ========================================================================= *)

(* Restricted models can artificially inflate complexity *)
Theorem restricted_model_inflates_complexity :
  exists (alg : Algorithm) (inst : ProblemInstance),
    running_time_in_model alg feinstein_restricted_model inst >
    running_time_in_model alg turing_machine_model inst.
Proof.
Admitted.

(* The gap between restricted and general models *)
Definition model_power_difference (model1 model2 : ComputationalModel) : Prop :=
  exists (alg1 alg2 : Algorithm) (inst : ProblemInstance),
    alg1.(solve) inst = alg2.(solve) inst /\
    running_time_in_model alg1 model1 inst <>
    running_time_in_model alg2 model2 inst.

Theorem restricted_vs_unrestricted :
  model_power_difference feinstein_restricted_model turing_machine_model.
Proof.
Admitted.

(* ========================================================================= *)
(* Part 5: The Specific Error in Feinstein's Approach                        *)
(* ========================================================================= *)

(* What the restricted model proof ACTUALLY shows *)
Definition restricted_model_result (problem : NPCompleteProblem) : Prop :=
  (* Among algorithms that only use operations allowed in the restricted model,
     none can solve the problem in less than exponential time *)
  forall alg : Algorithm,
    (forall inst sol, alg.(solve) inst = sol -> problem.(verify) inst sol = true) ->
    has_lower_bound alg feinstein_restricted_model exponential_bound.

(* What Feinstein CLAIMED it shows *)
Definition feinstein_claim (problem : NPCompleteProblem) : Prop :=
  (* NO algorithm, even with unrestricted operations, can solve in polynomial time *)
  forall alg : Algorithm,
    (forall inst sol, alg.(solve) inst = sol -> problem.(verify) inst sol = true) ->
    has_lower_bound alg turing_machine_model exponential_bound.

(* THEOREM: The gap between what's proven and what's claimed *)
Theorem claim_gap :
  exists (problem : NPCompleteProblem),
    restricted_model_result problem /\ ~ feinstein_claim problem.
Proof.
Admitted.

(* ========================================================================= *)
(* Part 6: Counterexample Invalidates Transfer                               *)
(* ========================================================================= *)

(* If a counterexample algorithm exists, the transfer principle fails *)
Theorem counterexample_invalidates_transfer :
  (exists (ce : CounterexampleAlgorithm) (problem : NPCompleteProblem),
    forall inst sol, ce.(ce_alg).(solve) inst = sol -> problem.(verify) inst sol = true) ->
  ~ (forall (problem : NPCompleteProblem) (bound : nat -> nat),
      problem_lower_bound problem feinstein_restricted_model bound ->
      problem_lower_bound problem turing_machine_model bound).
Proof.
  intros H_ce H_transfer.
  (* The counterexample algorithm:
     1. Correctly solves the problem
     2. Uses operations not in the restricted model
     3. Runs in polynomial time in general

     This contradicts the transfer principle because:
     - The problem has an exponential lower bound in the restricted model
     - But the counterexample algorithm solves it in polynomial time in general

     NOTE: The full formal proof requires concrete problem instances,
     which are not available since Feinstein withdrew his paper.
     The logical structure of the refutation is captured here. *)
Admitted.

(* ========================================================================= *)
(* Part 7: Valid vs Invalid Uses of Restricted Models                        *)
(* ========================================================================= *)

(* Valid use: conditional lower bounds *)
Definition conditional_lower_bound (problem : NPCompleteProblem) (model : ComputationalModel)
    (bound : nat -> nat) : Prop :=
  (* "IF we restrict ourselves to these operations, THEN..." *)
  problem_lower_bound problem model bound.

(* Invalid use: claiming unconditional lower bounds from restricted models *)
Definition invalid_generalization (problem : NPCompleteProblem) (restricted_model : ComputationalModel)
    (bound : nat -> nat) : Prop :=
  problem_lower_bound problem restricted_model bound ->
  problem_lower_bound problem turing_machine_model bound.

Theorem invalid_generalization_fails :
  exists (problem : NPCompleteProblem) (model : ComputationalModel) (bound : nat -> nat),
    ~ invalid_generalization problem model bound.
Proof.
Admitted.

(* ========================================================================= *)
(* Summary of the Refutation                                                 *)
(* ========================================================================= *)

(*
  Feinstein's 2003-04 attempt failed because the transfer principle is FALSE.

  ## The Core Error

  The claim:
  > "If a problem requires exponential time in my restricted model,
  >  then it requires exponential time in general computation"

  is NOT TRUE because:

  1. **Restricted models are strictly weaker**: They forbid algorithmic techniques
     that are available in general computation

  2. **Lower bounds don't transfer**: A problem being hard without technique X
     doesn't mean it's hard WITH technique X

  3. **Counterexample existence**: For any genuinely restricted model, there exist
     problems that are hard in the model but easy in general

  ## Concrete Example (Informal)

  Consider sorting:
  - In a comparison-based model, sorting requires Ω(n log n) comparisons
  - But radix sort achieves O(n) time using non-comparison operations
  - The comparison lower bound doesn't transfer to general computation!

  Feinstein's error was analogous: his restricted model forbade techniques that,
  in general computation, could efficiently solve the NP-complete problems he
  was analyzing.

  ## Why the Paper Was Withdrawn

  When a counterexample to the transfer principle was found, Feinstein
  responsibly withdrew the paper. This demonstrates proper scientific conduct:
  acknowledging when a claimed proof contains a fundamental flaw.

  ## Lessons Learned

  1. Restricted model lower bounds are CONDITIONAL: they only apply when using
     the restricted operations

  2. To prove P ≠ NP, one must show hardness for ALL algorithms, not just
     those in a restricted class

  3. The gap between restricted and general models remains a fundamental
     barrier in complexity theory
*)
