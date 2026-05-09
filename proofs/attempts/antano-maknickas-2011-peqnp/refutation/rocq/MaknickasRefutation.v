(**
  MaknickasRefutation.v - Refutation of Maknickas (2011) P=NP attempt

  This file demonstrates why Maknickas's approach fails:
  The LP relaxation of k-SAT does not preserve satisfiability, and the
  floor-modulo recovery function does not produce valid Boolean solutions.

  Reference: arXiv:1203.6020v2 [cs.CC] - "How to solve kSAT in polynomial time"
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Module MaknickasRefutationModule.

(** Literal, Clause, CNF definitions (same as in proof/) *)
Inductive Literal : Type :=
  | Pos : nat -> Literal
  | Neg : nat -> Literal.

Definition Clause := list Literal.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition eval_literal (a : Assignment) (l : Literal) : bool :=
  match l with
  | Pos n => a n
  | Neg n => negb (a n)
  end.

Fixpoint eval_clause (a : Assignment) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: ls => orb (eval_literal a l) (eval_clause a ls)
  end.

Fixpoint eval_cnf (a : Assignment) (f : CNF) : bool :=
  match f with
  | [] => true
  | c :: cs => andb (eval_clause a c) (eval_cnf a cs)
  end.

Definition Satisfiable (f : CNF) : Prop :=
  exists (a : Assignment), eval_cnf a f = true.

(** LP definitions (same as in proof/) *)
Definition RealAssignment := nat -> R.
Definition NonNegative (ra : RealAssignment) : Prop :=
  forall n, (ra n >= 0)%R.

Fixpoint clause_sum (ra : RealAssignment) (c : Clause) : R :=
  match c with
  | [] => 0%R
  | Pos n :: ls => (ra n + clause_sum ra ls)%R
  | Neg n :: ls => (ra n + clause_sum ra ls)%R
  end.

Definition lp_constraint_for_clause (ra : RealAssignment) (c : Clause) : Prop :=
  (clause_sum ra c <= INR (length c))%R.

Definition LPFeasible (f : CNF) (ra : RealAssignment) : Prop :=
  NonNegative ra /\ forall c, In c f -> lp_constraint_for_clause ra c.

Definition floor_mod2 (r : R) : bool :=
  match (Zeven_odd_dec (Int_part r)) with
  | left _ => true
  | right _ => false
  end.

Definition recover_assignment (ra : RealAssignment) : Assignment :=
  fun n => floor_mod2 (ra n).

(** ** Error 1: LP Relaxation Gap — Wrong Problem Being Solved *)
(**
  "Original problem: Find Xᵢ ∈ {0,1} such that CNF formula is TRUE"
  "Transformed problem: Find Xᵢ ∈ ℝ (Xᵢ ≥ 0) that satisfies ∑Xᵢ ≤ k"
  "These are completely different problems!"
*)

(** Counterexample: The clause (X₁ ∨ X₂ ∨ X₃)
    The LP solution X₁=X₂=X₃=1 satisfies the LP constraint (1+1+1 ≤ 3)
    but floor_mod2(1) = false, making all literals FALSE. *)

Definition clause3 : Clause := [Pos 1; Pos 2; Pos 3].
Definition formula3 : CNF := [clause3].

Definition bad_lp_solution : RealAssignment := fun _ => 1%R.

(** The bad LP solution satisfies the constraints *)
Lemma bad_lp_solution_feasible :
  LPFeasible formula3 bad_lp_solution.
Proof.
  unfold LPFeasible, NonNegative, lp_constraint_for_clause, formula3.
  split.
  - intro n. unfold bad_lp_solution. lra.
  - intros c [Heq | []]. subst.
    unfold clause3, clause_sum, bad_lp_solution.
    simpl. lra.
Qed.

(** The recovered Boolean assignment makes the clause FALSE.
    floor(1.0) = 1 is odd, so floor_mod2(1.0) = false.
    All three literals evaluate to false, so the clause is false. *)
Lemma bad_recovery_fails_on_clause3 :
  eval_clause (recover_assignment bad_lp_solution) clause3 = false.
Proof.
  unfold clause3, recover_assignment, bad_lp_solution, floor_mod2.
  simpl.
  (* We need: Int_part 1 is odd (= 1), so Zeven_odd_dec gives right *)
  replace (Int_part 1%R) with 1%Z.
  - simpl. reflexivity.
  - replace 1%R with (INR 1) by (simpl; lra). rewrite Int_part_INR. reflexivity.
Qed.

(** LP feasibility does NOT imply SAT satisfiability *)
Theorem lp_feasible_but_not_sat :
  LPFeasible formula3 bad_lp_solution /\
  eval_clause (recover_assignment bad_lp_solution) clause3 = false.
Proof.
  exact (conj bad_lp_solution_feasible bad_recovery_fails_on_clause3).
Qed.

(** ** Error 2: Negation is Completely Ignored *)
(**
  Maknickas's encoding treats (Xᵢ) and (¬Xᵢ) identically in LP constraints.
  The formula X₁ ∧ ¬X₁ is UNSATISFIABLE yet LP-feasible.
*)

Definition contradictory_formula : CNF := [[Pos 1]; [Neg 1]].

Theorem contradictory_is_unsat : ~ Satisfiable contradictory_formula.
Proof.
  intros [a Ha].
  unfold eval_cnf, contradictory_formula in Ha.
  simpl in Ha.
  destruct (a 1) eqn:Ha1.
  - simpl in Ha. discriminate.
  - simpl in Ha. discriminate.
Qed.

(** LP constraints for [Pos 1] and [Neg 1] are identical *)
Theorem negation_information_lost :
  forall ra,
    lp_constraint_for_clause ra [Pos 1] <->
    lp_constraint_for_clause ra [Neg 1].
Proof.
  intro ra.
  unfold lp_constraint_for_clause, clause_sum.
  simpl. tauto.
Qed.

(** The contradictory formula is LP-feasible (X₁ = 0 satisfies both) *)
Lemma contradictory_lp_feasible :
  exists ra, LPFeasible contradictory_formula ra.
Proof.
  exists (fun _ => 0%R).
  unfold LPFeasible, NonNegative, lp_constraint_for_clause, contradictory_formula.
  split.
  - intro n. lra.
  - intros c [Heq | [Heq | []]].
    + subst. simpl. lra.
    + subst. simpl. lra.
Qed.

(** ** Error 3: Problem Type Mismatch — LP Feasibility ≠ SAT Satisfiability *)

(** If the main claim were correct, LP feasibility would imply satisfiability.
    But contradictory_formula is LP-feasible yet unsatisfiable, contradiction! *)
Theorem problem_type_mismatch :
  ~ (forall f : CNF,
      (exists ra, LPFeasible f ra) ->
      Satisfiable f).
Proof.
  intro H.
  apply contradictory_is_unsat.
  apply H.
  exact contradictory_lp_feasible.
Qed.

(** ** Error 4: No Soundness Proof for the Recovery Function *)
(**
  The paper never proves that floor_mod2 converts LP solutions to valid SAT solutions.
  The main claim is not only unproven but false.
*)

(** The key claim the paper needs (which is false): *)
Theorem paper_main_claim_is_false :
  ~ (forall (f : CNF) (ra : RealAssignment),
      LPFeasible f ra ->
      eval_cnf (recover_assignment ra) f = true).
Proof.
  intro H.
  specialize (H formula3 bad_lp_solution bad_lp_solution_feasible).
  change (eval_cnf (recover_assignment bad_lp_solution) [clause3] = true) in H.
  unfold eval_cnf in H.
  rewrite bad_recovery_fails_on_clause3 in H.
  simpl in H. discriminate.
Qed.

(** ** Summary: Why Maknickas (2011) Does NOT Prove P = NP *)
(**
  The four fatal errors:
  1. LP RELAXATION GAP: LP constraints don't encode Boolean satisfiability
  2. NEGATION IGNORED: The encoding loses polarity information for literals
  3. WRONG PROBLEM: LP feasibility ≠ Boolean satisfiability
  4. UNPROVEN RECOVERY: floor_mod2 does not recover valid SAT solutions

  All four errors are formally demonstrated above with concrete counterexamples.
  Therefore, the paper does NOT establish k-SAT ∈ P, and does not prove P = NP.
*)

End MaknickasRefutationModule.
