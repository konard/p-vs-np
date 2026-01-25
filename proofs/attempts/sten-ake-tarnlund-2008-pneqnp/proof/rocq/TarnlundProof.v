(*
  TarnlundProof.v - Formalization of Tarnlund's 2008 P≠NP proof attempt structure
  Author: Formalization for p-vs-np repository
  Related: Issue #453
*)

Require Import String List Nat.

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

Theorem soundness_implies_truth :
  IsSoundForComplexity TheoryBPrime ->
  Provable TheoryBPrime SATNotInP_Formula ->
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP ->
  PNotEqualsNP.
Proof.
  intros soundness provable meaning.
  exact (soundness SATNotInP_Formula PNotEqualsNP meaning provable).
Qed.

Check soundness_implies_truth.
