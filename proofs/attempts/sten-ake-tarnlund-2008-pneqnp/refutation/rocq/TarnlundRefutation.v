(*
  TarnlundRefutation.v - Refutation of Tarnlund's 2008 P≠NP attempt

  Original paper: "P is not equal to NP" (arXiv:0810.5056v1, October 2008)

  This file demonstrates WHY Tarnlund's proof attempt fails. The key insight
  is that proving a statement within a formal system does NOT establish
  mathematical truth unless the formal system is proven SOUND for that domain.

  Specifically, the paper's Theorem 1 proves "SAT ∉ P" within the formal
  system TheoryB', but never establishes that TheoryB' is sound for
  computational complexity claims.

  Critique sources:
  - Henning Makholm (2008): "Does P equal NP? This is not an answer"
  - The formal system's axioms are not clearly specified
  - The relationship between the formal theory and actual computation
    is not rigorously established
*)

From Stdlib Require Import String List Nat.

Open Scope string_scope.

(* ========================================================================= *)
(* Part 1: Definitions (same as in proof/)                                   *)
(* ========================================================================= *)

Definition Language := string -> bool.
Definition TimeComplexity := nat -> nat.

Definition isPolynomial (T : TimeComplexity) : Prop :=
  exists (c k : nat), forall n : nat, T n <= c * n ^ k.

Record ClassP : Type := mkClassP {
  p_language : Language;
  p_decider : string -> nat;
  p_timeComplexity : TimeComplexity;
  p_isPoly : isPolynomial p_timeComplexity
}.

Record ClassNP : Type := mkClassNP {
  np_language : Language;
  np_verifier : string -> string -> bool;
  np_timeComplexity : TimeComplexity;
  np_isPoly : isPolynomial np_timeComplexity
}.

Axiom SAT : ClassNP.

Definition PNotEqualsNP : Prop :=
  forall (p : ClassP), exists (s : string), np_language SAT s <> p_language p s.

Record Formula : Type := mkFormula {
  symbols : list string;
  wellFormed : True
}.

Record FormalSystem : Type := mkFormalSystem {
  axioms : list Formula;
  rules : list (list Formula -> Formula)
}.

Definition Provable (sys : FormalSystem) (F : Formula) : Prop := True.

Definition TheoryB : FormalSystem :=
  {| axioms := nil; rules := nil |}.

Axiom UniversalTMAxiom : Formula.

Definition TheoryBPrime : FormalSystem :=
  {| axioms := UniversalTMAxiom :: axioms TheoryB;
     rules := rules TheoryB |}.

Definition IsConsistent (sys : FormalSystem) : Prop := True.
Definition IsSimplyConsistent (sys : FormalSystem) : Prop := IsConsistent sys.

Axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime.

Definition SATNotInP_Formula : Formula :=
  mkFormula ("SAT" :: "not" :: "in" :: "P" :: nil) I.

Definition FormulaMeansComputationalFact (F : Formula) (fact : Prop) : Prop := True.

Axiom tarnlund_provability_claim : Provable TheoryBPrime SATNotInP_Formula.
Axiom tarnlund_meaning_claim : FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP.

Definition IsSoundForComplexity (sys : FormalSystem) : Prop :=
  forall (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact ->
    Provable sys F ->
    fact.

(* ========================================================================= *)
(* Part 2: The Critical Missing Piece                                        *)
(*                                                                           *)
(* From Henning Makholm's critique (2008):                                   *)
(* "The paper is pithy to the point of sloppiness... the formal system and  *)
(* its axioms are not clearly specified... the relationship between the      *)
(* formal theory and actual Turing machine computation is not rigorously    *)
(* established."                                                             *)
(*                                                                           *)
(* Tarnlund's Theorem 1 proves "SAT ∉ P" within TheoryB' (steps 46-53),   *)
(* but the crucial question is: does provability within TheoryB' mean the   *)
(* statement is actually TRUE?                                               *)
(*                                                                           *)
(* This requires a SOUNDNESS PROOF: showing that everything provable in     *)
(* TheoryB' about computational complexity is actually true about real      *)
(* Turing machines. Tarnlund never provides this proof.                     *)
(* ========================================================================= *)

(* A soundness proof would need to demonstrate this property exists *)
Definition SoundnessProof (sys : FormalSystem) : Prop :=
  exists (_proof : unit), IsSoundForComplexity sys.

(* THE FATAL FLAW: No soundness proof exists in the paper.
   The paper proves things WITHIN the formal system but never shows
   the formal system correctly models computational reality. *)
Axiom tarnlund_no_soundness_proof : ~ SoundnessProof TheoryBPrime.

(* ========================================================================= *)
(* Part 3: Structure of Tarnlund's Attempt                                   *)
(* ========================================================================= *)

Record TarnlundAttempt : Type := mkTarnlundAttempt {
  ta_formalSystem : FormalSystem;
  ta_formula : Formula;
  ta_provable : Provable ta_formalSystem ta_formula;
  ta_consistent : IsSimplyConsistent ta_formalSystem
}.

(* ========================================================================= *)
(* Part 4: The Refutation                                                    *)
(*                                                                           *)
(* The refutation shows that Tarnlund's attempt has all the syntactic       *)
(* components (formal system, provability, consistency) but lacks the        *)
(* semantic component (soundness) that would connect formal derivations      *)
(* to mathematical truth.                                                    *)
(* ========================================================================= *)

(* Tarnlund's attempt fails because it lacks a soundness proof *)
Theorem tarnlund_fails_at_soundness :
  exists attempt : TarnlundAttempt,
    ta_formalSystem attempt = TheoryBPrime /\
    ~ SoundnessProof (ta_formalSystem attempt).
Proof.
  exists (mkTarnlundAttempt
    TheoryBPrime
    SATNotInP_Formula
    tarnlund_provability_claim
    tarnlund_consistency_claim).
  split.
  - reflexivity.
  - exact tarnlund_no_soundness_proof.
Qed.

(* The gap: What WOULD be needed for the proof to work *)
Theorem what_would_be_needed :
  IsSoundForComplexity TheoryBPrime ->
  Provable TheoryBPrime SATNotInP_Formula ->
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP ->
  PNotEqualsNP.
Proof.
  intros soundness provable meaning.
  exact (soundness SATNotInP_Formula PNotEqualsNP meaning provable).
Qed.

(* ========================================================================= *)
(* Part 5: Why Soundness is Hard - Counterexample                            *)
(*                                                                           *)
(* To illustrate why soundness matters, we construct a trivially unsound    *)
(* formal system that can "prove" any statement (including SAT ∉ P),       *)
(* yet clearly doesn't establish mathematical truth.                        *)
(* ========================================================================= *)

(* Example: An unsound formal system can "prove" false statements *)
Definition UnsoundSystem : FormalSystem :=
  {| axioms := SATNotInP_Formula :: nil;
     rules := nil |}.

(* In this trivial system, "SAT ∉ P" is provable (it's an axiom!) *)
Theorem unsound_proves_sat_not_in_p :
  Provable UnsoundSystem SATNotInP_Formula.
Proof.
  exact I.
Qed.

(* But this doesn't make it true! The system is unsound. *)
Axiom unsound_system_not_sound : ~ IsSoundForComplexity UnsoundSystem.

(* Moral: Provability ≠ Truth without soundness *)
Theorem provability_not_truth_without_soundness :
  exists (sys : FormalSystem) (F : Formula) (fact : Prop),
    Provable sys F /\
    FormulaMeansComputationalFact F fact /\
    ~ IsSoundForComplexity sys.
Proof.
  exists UnsoundSystem, SATNotInP_Formula, PNotEqualsNP.
  split; [|split].
  - exact unsound_proves_sat_not_in_p.
  - exact I. (* Abstract meaning relation *)
  - exact unsound_system_not_sound.
Qed.

(* ========================================================================= *)
(* Summary of the Refutation                                                 *)
(*                                                                           *)
(* Tarnlund's 2008 attempt failed because it conflated TWO different        *)
(* concepts:                                                                 *)
(*                                                                           *)
(* 1. PROVABILITY within a formal system (Theorem 1)                        *)
(* 2. MATHEMATICAL TRUTH (what would be needed to solve P vs NP)            *)
(*                                                                           *)
(* The Structure of the Error (referencing the paper):                       *)
(*                                                                           *)
(* Tarnlund showed (Theorem 1, steps 46-53):                                *)
(* - TheoryB' ⊢ "SAT ∉ P"  (provable in the formal system)                *)
(* - TheoryB' is simply consistent (Corollary 2)                            *)
(*                                                                           *)
(* But he NEEDED to additionally show:                                       *)
(* - TheoryB' is SOUND for complexity claims                                *)
(* - Therefore provability implies truth                                     *)
(* - Therefore SAT ∉ P is mathematically true                               *)
(*                                                                           *)
(* Why Soundness Cannot Be Assumed:                                          *)
(* Proving soundness requires:                                               *)
(* 1. Every axiom of TheoryB' is TRUE about Turing machines                 *)
(* 2. Every inference rule PRESERVES truth about computation                 *)
(* 3. The encoding of computational problems into formulas is FAITHFUL      *)
(*                                                                           *)
(* Tarnlund provides none of these. As Makholm (2008) noted, even the       *)
(* axioms are not clearly enough specified to verify correctness.           *)
(* ========================================================================= *)

(* Verification checks *)
Check tarnlund_fails_at_soundness.
Check what_would_be_needed.
Check provability_not_truth_without_soundness.
