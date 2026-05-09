(*
  TarnlundProof.v - Forward Formalization of Tarnlund's 2008 P≠NP Proof Attempt

  Original paper: "P is not equal to NP" (arXiv:0810.5056v1, October 2008)
  Author: Sten-Ake Tarnlund

  This file formalizes the structure of Tarnlund's attempted proof of P ≠ NP
  via a first-order theory of computing, following the paper's structure closely.

  The proof claims to show SAT ∉ P by contradiction using:
  1. A first-order theory B with axiom B characterizing a universal Turing machine
  2. A relationship between computing time and proof complexity (Lemma 3)
  3. Haken's theorem on resolution proof complexity of pigeonhole formulas
*)

From Stdlib Require Import String List Nat.

Open Scope string_scope.

(* ========================================================================= *)
(* Section 2: A Theory of Computing                                          *)
(* From the paper: "Before applying the axiomatic method to computing        *)
(* complexity, a first order theory B of computing, with a single finite     *)
(* axiom B characterizing a universal Turing machine, is presented."         *)
(* ========================================================================= *)

Definition Language := string -> bool.
Definition TimeComplexity := nat -> nat.

(* Definition 8: p(a) for c·|a|^q some c q ∈ ℕ *)
Definition isPolynomial (T : TimeComplexity) : Prop :=
  exists (c k : nat), forall n : nat, T n <= c * n ^ k.

(* Class P: polynomial-time decidable languages *)
Record ClassP : Type := mkClassP {
  p_language : Language;
  p_decider : string -> nat;
  p_timeComplexity : TimeComplexity;
  p_isPoly : isPolynomial p_timeComplexity
}.

(* Class NP: polynomial-time verifiable languages *)
Record ClassNP : Type := mkClassNP {
  np_language : Language;
  np_verifier : string -> string -> bool;
  np_timeComplexity : TimeComplexity;
  np_isPoly : isPolynomial np_timeComplexity
}.

Axiom SAT : ClassNP.

(* P ≠ NP statement *)
Definition PNotEqualsNP : Prop :=
  forall (p : ClassP), exists (s : string), np_language SAT s <> p_language p s.

(* ========================================================================= *)
(* Section 2: Formal System Definitions                                      *)
(* From the paper: "Syntactically, there are two predicate symbols of B      *)
(* written T(i, a, u), and U(x, s, z, q, j, i, u)."                        *)
(* ========================================================================= *)

(* Definition 3: Formulas of theory B *)
Record Formula : Type := mkFormula {
  symbols : list string;
  wellFormed : True
}.

(* A formal system with axioms and inference rules *)
Record FormalSystem : Type := mkFormalSystem {
  axioms : list Formula;
  rules : list (list Formula -> Formula)
}.

(* Provability in a formal system *)
Definition Provable (sys : FormalSystem) (F : Formula) : Prop := True.

(* ========================================================================= *)
(* Theory B and Axiom B (Axiom 1)                                           *)
(* From the paper (Axiom 1): "B for ∀ T(i,a,u) ⊃ U(∅,∅,a.∅,1,i,i,u) ..." *)
(* Six sentences (17)-(22) characterizing a universal Turing machine         *)
(* ========================================================================= *)

Definition TheoryB : FormalSystem :=
  {| axioms := nil; rules := nil |}.

(* Universal Turing Machine axiom (Axiom 1, sentences 17-22) *)
Axiom UniversalTMAxiom : Formula.

(* Theory B' (Theory B + Universal TM axiom, simply consistent extension) *)
Definition TheoryBPrime : FormalSystem :=
  {| axioms := UniversalTMAxiom :: axioms TheoryB;
     rules := rules TheoryB |}.

(* ========================================================================= *)
(* Section 2: Consistency Claims                                             *)
(* From the paper (Corollary 2):                                             *)
(* "Theory B is simply consistent in U i.e., there is no contradiction"     *)
(* ========================================================================= *)

Definition IsConsistent (sys : FormalSystem) : Prop := True.
Definition IsSimplyConsistent (sys : FormalSystem) : Prop := IsConsistent sys.

(* Corollary 2: Tarnlund claims TheoryB' is simply consistent *)
Axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime.

(* ========================================================================= *)
(* Section 2: Lemma 1                                                        *)
(* "Lemma 1: ∃uT(i,a,u) ⊃ ⊢ B → ∃uT(i,a,u) any i ∈ M a ∈ L."           *)
(* If a computation terminates, it is provable in theory B.                  *)
(* ========================================================================= *)

Axiom lemma1_computations_provable :
  forall (F : Formula), Provable TheoryBPrime F.

(* ========================================================================= *)
(* Section 3: Computing Time (Definitions 6-15)                              *)
(* Definition 15: SAT ∈ P for ⊢ B → ∃u T(i,F.∅,u) in p(F)                *)
(* ========================================================================= *)

Definition SATNotInP_Formula : Formula :=
  mkFormula ("SAT" :: "not" :: "in" :: "P" :: nil) I.

Definition FormulaMeansComputationalFact (F : Formula) (fact : Prop) : Prop := True.

(* Theorem 1: Tarnlund claims to prove "SAT ∉ P" in TheoryB' *)
Axiom tarnlund_provability_claim : Provable TheoryBPrime SATNotInP_Formula.

(* The formula is claimed to mean P ≠ NP *)
Axiom tarnlund_meaning_claim : FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP.

(* ========================================================================= *)
(* Section 4: Computing Time and Proof Complexity                            *)
(* Lemma 3 (Principal Lemma):                                               *)
(* "⊢ B → T(i,¬F.∅,∅.1) in p(F) ⊃ Y(i,F,n) ∧ n ≤ c·|F|^q"             *)
(* ========================================================================= *)

(* Definition 20: Y(i, F, n) formula
   Y(i,F,n) for (Q₀ ⊃ F) ∧ Qₙ ∧ ⋀₁≤k≤n (Qₖ ⊃ Qₖ₋₁) *)
Definition Y_formula (i : nat) (F : Formula) (n : nat) : Prop := True.

(* Lemma 3: Key claim linking computing time to proof complexity *)
Axiom lemma3_computing_time_proof_complexity :
  forall (i : nat) (F : Formula) (n : nat),
    Y_formula i F n.

(* ========================================================================= *)
(* Section 4.1: Proof Complexity and Haken's Theorem                         *)
(* "Every resolution proof of PFₙ contains at least cⁿ different clauses   *)
(* for c > 1 some c ∈ ℝ any sufficiently large n ∈ ℕ" (Haken 1985)        *)
(* ========================================================================= *)

(* Definition 22: Resolution provability *)
Definition ResolutionProvable (F : Formula) (size : nat) : Prop := True.

(* Haken's theorem *)
Axiom hakens_theorem :
  forall (m : nat), exists (minSize : nat),
    (forall (k : nat), minSize > k * m ^ k) /\
    forall (size : nat), size < minSize ->
      ~ ResolutionProvable (mkFormula ("PF" :: nil) I) size.

(* ========================================================================= *)
(* Main Results: Theorem 1 and Theorem 2                                     *)
(* Theorem 1 proof (steps 46-53):                                           *)
(* ⋆ SAT ∈ P (assumption for contradiction)                                 *)
(* ⋆ ⊢ B → T(i,¬F.∅,∅.1) in p(F)  (Corollary 5)                          *)
(* ⋆ Y(i,PFₘ,n) ∧ n ≤ c·|PFₘ|^q  (Lemma 3)                              *)
(* ⋆ ⊢_R PFₘ in p(PFₘ)  (from Y formula)                                  *)
(* ⋆ ¬(⊢_R PFₘ in p(PFₘ))  (Haken's theorem - CONTRADICTION)              *)
(* ⋆ SAT ∉ P                                                                *)
(* ========================================================================= *)

(* Soundness for computational complexity: provability implies truth *)
Definition IsSoundForComplexity (sys : FormalSystem) : Prop :=
  forall (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact ->
    Provable sys F ->
    fact.

(* IF soundness holds, THEN the proof works (valid part of argument) *)
Theorem soundness_implies_truth :
  IsSoundForComplexity TheoryBPrime ->
  Provable TheoryBPrime SATNotInP_Formula ->
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP ->
  PNotEqualsNP.
Proof.
  intros soundness provable meaning.
  exact (soundness SATNotInP_Formula PNotEqualsNP meaning provable).
Qed.

(* ========================================================================= *)
(* Summary of Tarnlund's Claimed Proof Structure                             *)
(*                                                                           *)
(* Tarnlund's approach:                                                      *)
(* 1. ✓ Defines a formal system TheoryB' (Section 2, Axiom 1)               *)
(* 2. ✓ Claims TheoryB' is simply consistent (Corollary 2)                  *)
(* 3. ✓ Establishes computing time / proof complexity relationship (Lemma 3)*)
(* 4. ✓ Uses Haken's theorem for contradiction (Theorem 1 proof)            *)
(* 5. ✗ MISSING: Proof that TheoryB' is SOUND for complexity claims         *)
(*                                                                           *)
(* The gap: Without soundness, provability in the system doesn't establish  *)
(* mathematical truth. The proof proves SAT ∉ P WITHIN the formal system,  *)
(* but never shows that this formal system correctly models reality.        *)
(*                                                                           *)
(* NOTE: We cannot formalize the soundness proof because it does not exist  *)
(* in Tarnlund's paper. This is the critical gap identified in the          *)
(* refutation.                                                               *)
(* ========================================================================= *)

Check soundness_implies_truth.
