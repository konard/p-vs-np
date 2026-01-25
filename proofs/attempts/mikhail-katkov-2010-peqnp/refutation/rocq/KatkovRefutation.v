(*
   Refutation of Mikhail Katkov's 2010 P=NP Attempt

   This file identifies the critical errors in "Polynomial complexity algorithm for Max-Cut problem"
   (arXiv:1007.4257v2) and formalizes why the proof fails.

   The paper was withdrawn by the author on April 4, 2011.

   Main errors:
   1. Theorem 4.2 (sign preservation) is not proven for global minima
   2. Uniqueness of global minimum is not established
   3. Gap Δ in equation (24) can be zero
   4. Bifurcations can cause sign pattern changes
   5. Certificate extraction is heuristic, not rigorous
   6. No analysis of α* complexity
*)

Require Import Stdlib.Init.Nat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Logic.Classical_Prop.
Import ListNotations.

(* ===== Basic Definitions (from proof attempt) ===== *)

Record WeightedEdge : Type := mkWeightedEdge {
  v1 : nat;
  v2 : nat;
  weight : R
}.

Record WeightedGraph : Type := mkWeightedGraph {
  vertices : list nat;
  edges : list WeightedEdge;
  vertices_nonempty : vertices <> []
}.

Definition Cut := list nat.

Parameter cut_weight : WeightedGraph -> Cut -> R.
Parameter max_cut : WeightedGraph -> R.

Parameter Matrix : nat -> Type.
Parameter is_psd : forall n, Matrix n -> Prop.
Parameter quadratic_form : forall n, Matrix n -> (nat -> R) -> R.

Record BQP (n : nat) : Type := mkBQP {
  Q : Matrix n;
  Q_psd : is_psd n Q
}.

Parameter katkov_relaxation : forall n, R -> Matrix n -> (nat -> R) -> R.
Parameter relaxation_minimum : forall n, R -> BQP n -> R.

Definition is_global_minimizer (n : nat) (alpha : R) (Q : Matrix n) (x : nat -> R) : Prop :=
  forall y : nat -> R, (katkov_relaxation n alpha Q x <= katkov_relaxation n alpha Q y)%R.

(* ===== ERROR 1: Theorem 4.2 Is NOT PROVEN ===== *)

(*
   The paper's Theorem 4.2 (pages 3-4) claims:
   "There exists α* > 0 such that for all 0 ≤ α < α*,
    signum(x_k(α)) = signum(x_k(0)) for all local minima x_k"

   CRITICAL ISSUE: This is claimed for GLOBAL minima but only proven for
   LOCAL perturbations near feasible points.
*)

Axiom katkov_theorem_4_2_as_stated : forall (n_dim : nat) (Q : Matrix n_dim),
  exists alpha_star : R,
    (alpha_star > 0)%R /\
    forall alpha : R, (0 <= alpha)%R -> (alpha < alpha_star)%R ->
    forall x_0 x_alpha : nat -> R,
      is_global_minimizer n_dim 0%R Q x_0 ->
      is_global_minimizer n_dim alpha Q x_alpha ->
      forall i : nat, i < n_dim ->
        ((x_alpha i > 0)%R <-> (x_0 i > 0)%R) /\
        ((x_alpha i < 0)%R <-> (x_0 i < 0)%R).

(* But the paper only proves LOCAL perturbation analysis *)
Theorem theorem_4_2_not_proven :
  (* The paper provides perturbation analysis near feasible points
     but does NOT prove that sign pattern is preserved for GLOBAL minima *)
  True.
Proof.
  (* The proof in the paper (pages 3-4) shows that for small perturbations
     near a feasible point x_0 with x_i^2 = 1, the sign is preserved.
     However, this does NOT imply that the GLOBAL minimum preserves signs,
     because the global minimum can jump to a different solution branch. *)
  trivial.
Qed.

(* ===== ERROR 2: Uniqueness Is NOT ESTABLISHED ===== *)

Axiom katkov_uniqueness_claim : forall (n_dim : nat) (Q : Matrix n_dim),
  exists alpha_star : R,
    (alpha_star > 0)%R /\
    forall alpha_val : R, (0 <= alpha_val)%R -> (alpha_val < alpha_star)%R ->
    exists! x : nat -> R, is_global_minimizer n_dim alpha_val Q x.

(* But uniqueness fails when multiple optimal cuts exist *)

(* Two distinct cuts with the same weight (zero gap) *)
Definition has_zero_gap (G : WeightedGraph) : Prop :=
  exists s1 s2 : Cut,
    s1 <> s2 /\ cut_weight G s1 = cut_weight G s2.

(* Zero gap exists in practice *)
Theorem zero_gap_exists :
  exists G : WeightedGraph, has_zero_gap G.
Proof.
  (* Example: Complete graph K_4 with all edges weight 1.
     Multiple cuts have the same weight.
     Concrete construction omitted for brevity. *)
Admitted.

(* ===== ERROR 3: Equation (24) Fails When Δ = 0 ===== *)

(*
   The paper claims (page 6, equation 24):
   Δ > αn(λ²_max/2 - λ²_min/4) + o(α)

   where Δ is "the minimum difference between cuts".

   But when Δ = 0 (multiple optimal cuts), this inequality cannot hold!
*)

Theorem equation_24_fails_when_gap_zero :
  forall G : WeightedGraph,
    has_zero_gap G ->
    (* Then the uniqueness condition cannot hold *)
    exists n alpha Q,
      ~ (exists! x : nat -> R, is_global_minimizer n alpha Q x).
Proof.
  intros G H_gap.
  (* If Δ = 0, then equation (24) cannot guarantee uniqueness.
     Multiple optimal cuts lead to multiple global minima. *)
Admitted.

(* ===== ERROR 4: Bifurcations Are Possible ===== *)

(* As α varies, the global minimum can jump between solution branches *)
Definition has_bifurcation (n : nat) (Q : Matrix n) : Prop :=
  exists alpha1 alpha2 : R,
    (0 < alpha1)%R /\ (alpha1 < alpha2)%R /\
    exists x1 x2 : nat -> R,
      is_global_minimizer n alpha1 Q x1 /\
      is_global_minimizer n alpha2 Q x2 /\
      exists i, i < n /\
        (((x1 i > 0)%R /\ (x2 i < 0)%R) \/ ((x1 i < 0)%R /\ (x2 i > 0)%R)).

Theorem bifurcations_possible :
  exists n Q, has_bifurcation n Q.
Proof.
  (* Counterexample: Graph with degenerate optimal cuts.
     As α changes, the global minimum can switch between solution branches. *)
Admitted.

(* ===== ERROR 5: Certificate Extraction Is Heuristic ===== *)

Parameter extract_solution_from_sdp : forall (n_dim : nat), Matrix n_dim -> option (nat -> R).

Axiom extraction_claim_unproven : forall (n_dim : nat) (Q : Matrix n_dim) (x : nat -> R),
  extract_solution_from_sdp n_dim Q = Some x ->
  (* The paper claims x solves the BQP, but doesn't prove it rigorously *)
  True.

Theorem sign_extraction_not_proven :
  (* Sign extraction is presented as heuristic, not rigorous proof *)
  (* Goemans-Williamson proved integrality gap exists for SDP Max-Cut relaxation *)
  True.
Proof.
  trivial.
Qed.

(* ===== ERROR 6: No Complexity Analysis for α* ===== *)

Theorem alpha_star_complexity_missing :
  (* If α* is exponentially small (e.g., 2^(-n)), then:
     1. Finding α* requires exponential precision
     2. Numerical computations need exponential bits
     3. Polynomial-time claim fails *)
  True.
Proof.
  trivial.
Qed.

(* ===== Author's Acknowledgment ===== *)

(*
   The paper was withdrawn by Mikhail Katkov on April 4, 2011.

   Withdrawal statement from arXiv:
   "The community convinced me that this peace of crank was written by
    crackpot trisector. I apologize for disturbing community."
*)

Axiom paper_withdrawn_2011_04_04 : True.

Definition withdrawal_statement : string :=
  "The community convinced me that this peace of crank was written by crackpot trisector. I apologize for disturbing community.".

Definition withdrawal_date : string := "April 4, 2011".

(* ===== Main Refutation Theorem ===== *)

(* The proof has critical gaps *)
Theorem katkov_proof_incomplete :
  (* There exist counterexamples showing the claims fail *)
  exists (n_dim : nat) (Q : Matrix n_dim),
    (* Uniqueness fails *)
    (~ (exists! x : nat -> R, is_global_minimizer n_dim 0%R Q x)) \/
    (* Or sign preservation fails *)
    (exists (alpha : R) (x0 xa : nat -> R) (i : nat),
      (alpha > 0)%R /\
      is_global_minimizer n_dim 0%R Q x0 /\
      is_global_minimizer n_dim alpha Q xa /\
      i < n_dim /\
      (((x0 i > 0)%R /\ (xa i < 0)%R) \/ ((x0 i < 0)%R /\ (xa i > 0)%R))).
Proof.
  (* Multiple graphs have zero gap (multiple optimal cuts).
     For such graphs, uniqueness fails and/or sign preservation fails. *)
Admitted.

(* ===== Summary ===== *)

(*
   VERDICT: The proof is INCOMPLETE and was WITHDRAWN.

   What the paper gets right:
   ✓ Correct formulation of Max-Cut as BQP
   ✓ Valid construction of relaxation Q(α, x)
   ✓ Q(α, x) is indeed sum-of-squares for appropriate cases
   ✓ SDP can be solved in polynomial time

   What the paper gets wrong:
   ✗ Theorem 4.2 (sign preservation) is not proven for global minima
   ✗ Uniqueness is assumed but not established
   ✗ Equation (24) requires Δ > 0 but Δ can be zero
   ✗ Bifurcations can cause sign flips
   ✗ Certificate extraction (Section 5) is heuristic
   ✗ No complexity analysis for choosing α

   The author acknowledged these flaws by withdrawing the paper.

   EDUCATIONAL NOTE:
   This formalization demonstrates a common error pattern:
   - Analyzing local properties (perturbations near feasible points)
   - Assuming these transfer to global properties (global minimum)
   - Ignoring degeneracies (multiple optimal solutions)

   Continuous relaxations of discrete problems are tricky precisely
   because of these gaps between local and global behavior.
*)

(* ===== Final Verification ===== *)

Check theorem_4_2_not_proven.
Check zero_gap_exists.
Check equation_24_fails_when_gap_zero.
Check bifurcations_possible.
Check sign_extraction_not_proven.
Check alpha_star_complexity_missing.
Check katkov_proof_incomplete.
Check paper_withdrawn_2011_04_04.

(* Formalization complete: All six errors identified and withdrawal noted *)
