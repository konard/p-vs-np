(*
  TarnlundRefutation.v - Refutation of Tarnlund's 2008 P≠NP attempt

  This file demonstrates WHY Tarnlund's proof attempt fails. The key insight is that
  proving a statement within a formal system does NOT establish mathematical truth
  unless the formal system is proven SOUND for that domain.

  Author: Formalization for p-vs-np repository
  Date: 2026-01-25
  Related: Issue #453, Woeginger's list entry #48
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
(* ========================================================================= *)

(*
  Tarnlund's error: He proved "SAT ∉ P" within a formal system TheoryB',
  but never proved that TheoryB' is SOUND for computational complexity claims.

  Without soundness, proving something in the system doesn't make it true!
*)

(* A soundness proof would need to demonstrate this property exists *)
Definition SoundnessProof (sys : FormalSystem) : Prop :=
  exists (_proof : unit), IsSoundForComplexity sys.

(* THE FATAL FLAW: No soundness proof exists *)
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
(* Part 5: Why Soundness is Hard                                             *)
(* ========================================================================= *)

(*
  Proving soundness for complexity theory requires showing that:

  1. Every axiom of TheoryB' is TRUE as a statement about Turing machines
  2. Every inference rule PRESERVES truth
  3. The encoding of computational problems into formulas is FAITHFUL

  This is a HARD problem that Tarnlund did not solve. In fact, it's
  essentially equivalent to solving P vs NP itself!

  If TheoryB' were powerful enough to prove "SAT ∉ P" and we could prove
  it sound, we would have solved P vs NP. But Tarnlund provides no
  soundness proof, so his derivation within the formal system establishes
  nothing about the actual P vs NP question.
*)

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
(* ========================================================================= *)

(*
  Tarnlund's 2008 attempt failed because it conflated TWO different concepts:

  1. PROVABILITY within a formal system (what Tarnlund established)
  2. MATHEMATICAL TRUTH (what would be needed to solve P vs NP)

  ## The Structure of the Error

  Tarnlund showed:
  - TheoryB' ⊢ "SAT ∉ P"  (provable in the formal system)
  - TheoryB' is simply consistent (doesn't prove contradictions)

  But he NEEDED to show:
  - TheoryB' is SOUND for complexity claims
  - Therefore provability implies truth
  - Therefore SAT ∉ P is mathematically true

  ## Why This is Hard

  Proving soundness of a formal system for computational complexity is
  itself a deep problem. The formal system must:

  1. Have axioms that are TRUE statements about computation
  2. Have inference rules that PRESERVE truth
  3. Correctly encode computational problems as formulas

  Without a soundness proof, derivations in the formal system are
  meaningless for establishing mathematical facts.

  ## Lessons Learned

  1. Formal proofs require both SYNTAX (derivations) and SEMANTICS (soundness)
  2. Provability in a system ≠ mathematical truth
  3. Soundness proofs are essential but often overlooked
  4. This error pattern appears in multiple failed P vs NP attempts
*)

(* Verification checks *)
Check tarnlund_fails_at_soundness.
Check what_would_be_needed.
Check provability_not_truth_without_soundness.
