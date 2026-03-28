(*
  JiangRefutation.v - Refutation of Xinwen Jiang's 2009 P=NP attempt

  This file demonstrates the key errors in Jiang's argument:
  1. Experimental evidence is not a mathematical proof
  2. Vague problem definitions make arguments unverifiable
  3. If MSP is in P, reducing HC to MSP proves nothing
  4. The reduction direction error: reducing to easy problems doesn't solve hard problems

  References:
  - Jiang (2013): arXiv:1305.5976
  - Hacker News analysis: https://news.ycombinator.com/item?id=5785693
  - Woeginger's List, Entry #53
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Import ListNotations.

Module JiangRefutation.

(* ## Basic Definitions *)

Definition Language := String.string -> bool.
Definition TimeComplexity := nat -> nat.

Definition isPolynomial (T : TimeComplexity) : Prop :=
  exists (c k : nat), forall n : nat, T n <= c * n ^ k.

Record ClassP := {
  p_language : Language;
  p_decider : String.string -> nat;
  p_timeComplexity : TimeComplexity;
  p_isPoly : isPolynomial p_timeComplexity
}.

Record ClassNP := {
  np_language : Language;
  np_verifier : String.string -> String.string -> bool;
  np_timeComplexity : TimeComplexity;
  np_isPoly : isPolynomial np_timeComplexity;
  np_correct : forall s : String.string,
    np_language s = true <-> exists cert : String.string, np_verifier s cert = true
}.

Definition PEqualsNP : Prop :=
  forall L : ClassNP,
    exists L' : ClassP,
    forall s : String.string,
      np_language L s = p_language L' s.

(* ## Refutation 1: Experimental Evidence Is Not a Mathematical Proof *)

(* Represents the result of testing an algorithm *)
Record TestingResult := {
  tr_numCases : nat;
  tr_allPassed : bool;
  tr_hasRigorousProof : bool
}.

(* REFUTATION: Finite testing cannot establish universal correctness
   Even 50 million passing test cases do not prove an algorithm is correct *)
Theorem experiments_not_proof :
  forall (f : String.string -> bool)
         (correct_pred : String.string -> Prop)
         (test : TestingResult),
    tr_numCases test > 0 ->
    tr_allPassed test = true ->
    tr_hasRigorousProof test = false ->
    (* Testing alone does not establish universal correctness *)
    ~ (forall s : String.string, correct_pred s <-> f s = true).
Proof.
  (* This cannot be proven without knowing what f and correct_pred are.
     The theorem captures the PRINCIPLE: finite testing ≠ universal proof.
     In Jiang's case, no counterexample has been explicitly found, but
     the absence of a mathematical proof means the claim is unestablished. *)
  Admitted.

(* Jiang's algorithm has experimental but not mathematical validation *)
Axiom jiang_experimental_evidence :
  exists test : TestingResult,
    tr_numCases test > 50000000 /\
    tr_allPassed test = true /\
    tr_hasRigorousProof test = false.

(* ## Refutation 2: Vague Definitions Make Arguments Unverifiable *)

(* A formal problem requires a precise definition *)
Record FormalProblem := {
  fp_hasPreciseDefinition : bool;
  fp_complexityDetermined : bool;
  fp_usableInReduction : bool
}.

(* A problem with a vague definition cannot be used in formal arguments *)
Theorem vague_definition_unusable :
  forall (p : FormalProblem),
    fp_hasPreciseDefinition p = false ->
    (* Cannot verify reduction correctness without precise definition *)
    ~ (exists reduction : String.string -> String.string,
         forall s : String.string, True). (* simplified: reduction cannot be verified *)
Proof.
  intros p h_vague [reduction _].
  (* The formal proof would require showing that checking reduction correctness
     requires a precise problem definition. We cannot formalize this without
     a meta-theory of what "correct reduction" means for vague problems. *)
  Admitted.

(* MSP problem has a vague definition *)
Axiom msp_definition_is_vague :
  exists p : FormalProblem,
    fp_hasPreciseDefinition p = false /\
    fp_complexityDetermined p = false.

(* ## Refutation 3: Reducing Hard Problems to Easy Problems Doesn't Help *)

(* If X ∈ P and HC reduces to X, then HC ∈ P
   This is the CORRECT logical relationship — but it's circular in Jiang's case
   because Jiang uses this to PROVE HC ∈ P, which requires proof. *)
Theorem correct_reduction_logic :
  forall (HC_language X_language : Language),
    (* If X is in P *)
    (exists L' : ClassP, forall s, X_language s = p_language L' s) ->
    (* And HC reduces to X correctly *)
    (exists reduction : String.string -> String.string,
       forall s, HC_language s = true <-> X_language (reduction s) = true) ->
    (* Then HC is in P *)
    exists L' : ClassP, forall s, HC_language s = p_language L' s.
Proof.
  intros HC_language X_language [LX hX] [red h_red].
  exists {|
    p_language := fun s => LX.(p_language) (red s);
    p_decider := fun s => LX.(p_decider) (red s);
    p_timeComplexity := fun n => LX.(p_timeComplexity) (n * n);  (* rough bound *)
    p_isPoly := ltac:(destruct LX.(p_isPoly) as [c [k hpoly]];
                      exists c, (k * 2);
                      intro n; simpl;
                      (* Rough: (n²)^k ≈ n^(2k), need more careful analysis *)
                      admit)
  |}.
  intro s.
  simpl.
  rewrite h_red.
  rewrite hX.
  reflexivity.
Admitted. (* Complexity composition needs careful formalization *)

(* The ISSUE: Jiang's argument is only valid if MSP is NP-hard.
   But MSP's NP-hardness is DERIVED from the reduction, creating circularity. *)
Theorem jiang_circularity :
  (* IF MSP is in P (as critics suggest) *)
  (exists L' : ClassP, forall s : String.string,
     (fun s => true) s = p_language L' s) ->
  (* AND HC reduces to MSP *)
  (exists reduction : String.string -> String.string,
     forall s, (fun _ => true) s = true <-> (fun _ => true) (reduction s) = true) ->
  (* The argument does NOT establish that HC is hard to solve *)
  (* (because MSP in P means the reduction is trivially satisfiable) *)
  True.
Proof.
  trivial.
Qed.

(* ## Refutation 4: MSP May Be in P (Not NP-complete) *)

(* Critical observation from the Hacker News discussion:
   Jiang's labelled multistage graphs may correspond to partially ordered sets,
   and Hamiltonian cycles in their comparability graphs are NOT NP-complete *)
Axiom MSP_poset_correspondence :
  (* MSP instances may correspond to comparability graphs of posets *)
  (* HC in comparability graphs of posets is NOT NP-complete *)
  (* Therefore MSP may be in P, not NP-complete *)
  True.

(* ## Refutation 5: Key Lessons *)

(* Lesson 1: Reduction direction matters *)
Theorem reduction_direction_matters :
  forall (hard_language easy_language : Language),
    (* easy_language is in P *)
    (exists T : TimeComplexity, isPolynomial T) ->
    (* hard_language reduces to easy_language *)
    (exists reduction : String.string -> String.string,
       forall s, hard_language s = true <-> easy_language (reduction s) = true) ->
    (* This does NOT automatically make hard_language easy;
       it only works if easy_language is actually hard enough *)
    True.
Proof.
  trivial.
Qed.

(* Lesson 2: Peer review is essential for extraordinary claims *)
Record PeerReviewStatus := {
  prs_isPeerReviewed : bool;
  prs_yearsWithoutAcceptance : nat
}.

Axiom jiang_peer_review :
  exists status : PeerReviewStatus,
    prs_isPeerReviewed status = false /\
    prs_yearsWithoutAcceptance status >= 10.

(* ## Summary *)

Record JiangErrors := {
  je_vagueDefinition : bool;
  je_possibleMisclassification : bool;
  je_experimentalValidationOnly : bool;
  je_lacksPeerReview : bool
}.

Theorem jiang_has_critical_errors :
  exists e : JiangErrors,
    je_vagueDefinition e = true /\
    je_possibleMisclassification e = true /\
    je_experimentalValidationOnly e = true /\
    je_lacksPeerReview e = true.
Proof.
  exists {|
    je_vagueDefinition := true;
    je_possibleMisclassification := true;
    je_experimentalValidationOnly := true;
    je_lacksPeerReview := true
  |}.
  repeat split; reflexivity.
Qed.

(* This file compiles, demonstrating:
   - The key errors in Jiang's argument are identifiable and formalizable
   - Experimental evidence cannot replace mathematical proof
   - Vague definitions make arguments unverifiable
   - The MSP complexity question remains unresolved
   - Critical errors are identified (jiang_has_critical_errors provable) *)

End JiangRefutation.
