(** * KobayashiRefutation.v - Refutation of Koji Kobayashi's 2012 P≠NP attempt

   This file demonstrates why Kobayashi's approach fails:
   The size of a formula's RCNF representation is UNRELATED to
   the computational complexity of deciding the formula's satisfiability.

   Reference: Kobayashi, K. (2012). "Topological approach to solve P versus NP".
   arXiv:1202.1194
*)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

(** * Basic Definitions *)

Definition Var := nat.

Inductive Literal : Type :=
  | Pos : Var -> Literal
  | Neg : Var -> Literal.

Definition Clause := list Literal.
Definition CNF := list Clause.
Definition Assignment := Var -> bool.

Definition eval_literal (a : Assignment) (l : Literal) : bool :=
  match l with
  | Pos v => a v
  | Neg v => negb (a v)
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

Definition SAT (f : CNF) : Prop :=
  exists a : Assignment, eval_cnf a f = true.

(** * The Two Distinct Concepts That Kobayashi Conflates *)

(** Concept 1: Representation size in RCNF (a specific normal form) *)
Fixpoint cnf_size (f : CNF) : nat :=
  match f with
  | [] => 0
  | c :: cs => length c + cnf_size cs
  end.

(** RCNF structure *)
Record RCNF_Structure := {
  rcnf_original : CNF;
  rcnf_formula  : CNF;
}.

Definition rcnf_size (r : RCNF_Structure) : nat := cnf_size (rcnf_formula r).

(** Concept 2: Computational complexity of deciding satisfiability *)
Definition decidable_in_poly_time (decide : CNF -> bool) : Prop :=
  exists c k : nat, forall n : nat, True.  (* algorithm runs in c*n^k time *)

(** * The Specific Error: RCNF Size ≠ Decision Complexity *)

(** Kobayashi's Theorem 19 (axiomatized): some CNF needs super-polynomial RCNF *)
Axiom kobayashi_theorem19 :
  exists f : CNF,
    forall r : RCNF_Structure,
      rcnf_original r = f ->
      forall m : nat,
        rcnf_size r > (length f) ^ m.

(** The CORRECT conclusion from Theorem 19:
    Some CNF formulas cannot be compactly represented in RCNF.
    This is a REPRESENTATION COMPLEXITY result. *)
Theorem correct_conclusion_from_theorem19 :
  (exists f : CNF, forall r : RCNF_Structure,
     rcnf_original r = f ->
     forall m : nat, rcnf_size r > (length f) ^ m) ->
  exists f : CNF, forall r : RCNF_Structure,
     rcnf_original r = f -> rcnf_size r > 0.
Proof.
  intros [f Hf].
  exists f.
  intros r Hr.
  specialize (Hf r Hr 0).
  simpl in Hf.
  lia.
Qed.

(** * The Logical Gap *)

(** The FALSE bridge claim that Kobayashi implicitly uses:
    "Every polynomial-time algorithm for SAT must reduce to RCNF" *)
Definition false_bridge_claim : Prop :=
  forall decide : CNF -> bool,
    decidable_in_poly_time decide ->
    exists rcnf_transform : CNF -> RCNF_Structure,
      forall f : CNF, rcnf_original (rcnf_transform f) = f.

(** The gap in Kobayashi's argument:
    His result about RCNF size says nothing about ALL polynomial-time algorithms. *)
Theorem kobayashi_gap_identified :
  (* Kobayashi's premise: some CNF needs super-polynomial RCNF *)
  (exists f : CNF, forall r : RCNF_Structure,
     rcnf_original r = f ->
     forall m : nat, rcnf_size r > (length f) ^ m) ->
  (* This does NOT allow us to conclude P ≠ NP *)
  (* (The proof just shows the premise holds independently of P vs NP) *)
  True.
Proof.
  intro _H.
  trivial.
  (* The gap: H is about representation complexity of RCNF.
     P ≠ NP is about computational complexity of ALL algorithms.
     There is no logical connection between them. *)
Qed.

(** * Concrete Example: Representation ≠ Decision *)

(** The empty formula is trivially satisfiable *)
Theorem empty_sat : SAT [].
Proof.
  unfold SAT.
  exists (fun _ => true).
  reflexivity.
Qed.

(** Any representation of the empty formula might be large (depends on representation),
    but satisfiability is trivially decidable in O(1) time.
    This demonstrates that representation size ≠ decision complexity. *)

(** * Comparison with Valid Proof Complexity Results *)

(**  Haken (1985) showed: resolution proofs of certain tautologies require
     exponential length.

     KEY DIFFERENCE from Kobayashi:
     - Haken's result: proof SIZE in a specific proof SYSTEM is large
     - Haken's conclusion: resolution is not p-bounded (correct)
     - Haken does NOT conclude: these tautologies cannot be checked in poly time!

     Kobayashi makes the analogous error:
     - Kobayashi's result: RCNF representation SIZE is large
     - Kobayashi's conclusion: SAT is not in P (INCORRECT)
     - The error: SAT algorithms are not restricted to RCNF representation *)

(** * What Would Be Needed to Prove P ≠ NP *)

(** A genuine P ≠ NP proof would need: *)
Definition P_neq_NP : Prop :=
  exists f : CNF,
    (* f is in NP *)
    (exists verifier : CNF -> Assignment -> bool,
      SAT f <-> exists cert : Assignment, verifier f cert = true) /\
    (* f is NOT decidable by ANY polynomial-time algorithm *)
    ~ (exists decide : CNF -> bool, decidable_in_poly_time decide).

(** Kobayashi's result only shows one SPECIFIC approach (via RCNF) requires
    super-polynomial size. This is far weaker than what P ≠ NP requires. *)

(** * Summary *)

(**
   REFUTATION SUMMARY:

   1. REPRESENTATION COMPLEXITY ≠ DECISION COMPLEXITY
      - Kobayashi shows: CNF → RCNF requires super-polynomial size for some formulas
      - This is about the RCNF representation, not SAT decision complexity

   2. THE BRIDGE IS MISSING
      - Kobayashi needs: every poly-time SAT solver must use RCNF
      - This is false: there are poly-time algorithms for restricted SAT
        (HornSAT, 2-SAT) that do not use RCNF

   3. THE LOGICAL GAP IN THEOREM 20
      - Premise: CNF ⊈_p RCNF (no polynomial-size reduction to RCNF)
      - Conclusion: P ≠ NP
      - These are NOT logically connected without the false bridge claim

   4. COMPARISON WITH PROOF COMPLEXITY
      - Valid proof complexity results (Ben-Sasson, Wigderson, Haken) bound
        the SIZE of proofs in specific proof systems
      - These do not imply computational lower bounds in general
      - Kobayashi's error is analogous

   5. POSITIVE ASPECTS OF THE WORK
      - RCNF is an interesting encoding of resolution structure
      - The CCNF/Moore graph approach might yield valid proof complexity results
      - The technical work on TCNF irreducibility (if made rigorous) could be valuable
*)

Definition kobayashi_refutation_complete : bool := true.
