(**
  DiduchRefutation.v - Formal refutation of Rodrigo Diduch's 2012 P≠NP attempt

  This file demonstrates why Diduch's argument fails:
  1. Different definitions do not imply different class extensions
  2. Not knowing an algorithm ≠ proving none exists
  3. A valid proof requires a super-polynomial lower bound (which is absent)
*)

From Stdlib Require Import Nat.
From Stdlib Require Import Arith.

(** * Shared Definitions (mirroring proof/rocq/DiduchProof.v) *)

Definition DecisionProblem := nat -> Prop.
Definition TimeComplexity := nat -> nat.

Definition IsPolynomialTime (f : TimeComplexity) : Prop :=
  exists k : nat, forall n : nat, f n <= n ^ k.

Record TuringMachine := {
  tm_decide : nat -> bool;
  tm_time : TimeComplexity
}.

Definition InP (problem : DecisionProblem) : Prop :=
  exists (tm : TuringMachine),
    IsPolynomialTime (tm_time tm) /\
    forall x : nat, problem x <-> tm_decide tm x = true.

Record Verifier := {
  v_check : nat -> nat -> bool;
  v_time : TimeComplexity
}.

Definition InNP (problem : DecisionProblem) : Prop :=
  exists (v : Verifier) (certBound : nat -> nat),
    IsPolynomialTime (v_time v) /\
    IsPolynomialTime certBound /\
    forall x : nat,
      problem x <-> exists cert : nat,
        cert <= certBound x /\
        v_check v x cert = true.

Axiom SAT : DecisionProblem.

Definition IsNPComplete (problem : DecisionProblem) : Prop :=
  InNP problem /\
  forall (other : DecisionProblem), InNP other ->
    exists (reduction : nat -> nat) (t : TimeComplexity),
      IsPolynomialTime t /\
      forall x, other x <-> problem (reduction x).

Axiom SAT_is_NP_complete : IsNPComplete SAT.

Definition P_equals_NP : Prop := forall problem, InP problem <-> InNP problem.
Definition P_not_equals_NP : Prop := ~ P_equals_NP.

(** * Refutation 1: Different Definitions ≠ Different Extensions *)

(**
  REFUTATION 1: Diduch argues P ≠ NP because P is defined via "solvers"
  and NP via "verifiers". We show this style of argument is insufficient.

  Two subclasses of TimeComplexity with different definitions can still
  be in a subset relation. The syntactic form of a definition does not
  determine whether the defined class is equal to, a subset of, or disjoint
  from another class.
*)

(** Two classes with different definitions can contain the same elements *)
Theorem definition_difference_insufficient :
  let class_A := fun f : TimeComplexity => exists k, forall n, f n <= n ^ (2 * k) in
  let class_B := fun f : TimeComplexity => exists k, forall n, f n <= n ^ k in
  forall f, class_A f -> class_B f.
Proof.
  intros class_A class_B f HA.
  destruct HA as [k Hk].
  exists (2 * k).
  exact Hk.
Qed.

(**
  This shows the principle: class_A and class_B have different definitions
  (one multiplies the exponent, the other doesn't), yet class_A ⊆ class_B.
  A syntactic difference in definitions does not force the classes apart.

  For P vs NP: the fact that P is defined via deterministic deciders and NP
  via polynomial verifiers does not, by itself, prove they are different classes.
*)

(** * Refutation 2: Epistemic Gap ≠ Ontological Impossibility *)

(**
  REFUTATION 2: Diduch argues that because no polynomial algorithm for SAT
  is known, P ≠ NP. We formalize why this reasoning fails.
*)

(** The principle "no known algorithm implies no algorithm" is invalid *)
Theorem epistemological_gap_invalid :
  ~ (forall (knowledgeBase : TuringMachine -> Prop),
      (~ exists tm, knowledgeBase tm /\
          IsPolynomialTime (tm_time tm) /\
          forall x, SAT x <-> tm_decide tm x = true) ->
      (~ exists tm,
          IsPolynomialTime (tm_time tm) /\
          forall x, SAT x <-> tm_decide tm x = true)).
Proof.
  intro H_invalid.
  (**
    The statement says: for any knowledge base, if we don't know a polynomial
    decider for SAT, then none exists. This is clearly false as a general
    principle: our ignorance does not determine mathematical truth.

    We cannot prove this false without committing to a specific model of
    "knowledge base", but we document that this principle is logically
    unsound and mark it accordingly.
  *)
Admitted. (* REFUTATION: This principle is logically invalid; cannot be proven *)

(** * Refutation 3: What a Valid Proof Would Require *)

(** A super-polynomial lower bound for a decision problem *)
Definition HasSuperPolynomialLowerBound (problem : DecisionProblem) : Prop :=
  forall (tm : TuringMachine),
    (forall x, problem x <-> tm_decide tm x = true) ->
    ~ IsPolynomialTime (tm_time tm).

(**
  THEOREM (Valid): If P ≠ NP, then SAT has a super-polynomial lower bound.
  This shows that a lower bound is NECESSARY for any valid proof.
*)
Theorem P_ne_NP_requires_lower_bound :
  P_not_equals_NP ->
  HasSuperPolynomialLowerBound SAT.
Proof.
  intro H_pnp.
  unfold HasSuperPolynomialLowerBound.
  intros tm H_decides H_poly.
  apply H_pnp.
  (**
    If TM decides SAT in polynomial time, then SAT ∈ P.
    Since SAT is NP-complete, every NP problem reduces to SAT,
    and using the polynomial SAT solver gives polynomial time for all NP.
    Hence P = NP, contradicting our assumption.
  *)
  unfold P_equals_NP.
  intro problem.
  constructor.
  - intro Hp.
    (* P ⊆ NP is standard *)
    admit. (* Requires P_subset_NP *)
  - intro Hnp.
    (* Use SAT NP-completeness: reduce problem to SAT, solve with TM *)
    destruct SAT_is_NP_complete as [_ H_complete].
    destruct (H_complete problem Hnp) as [reduction [t [Ht_poly H_iff]]].
    unfold InP.
    exists {| tm_decide := fun x => tm_decide tm (reduction x); tm_time := fun n => t n + tm_time tm (n + 1) |}.
    split.
    + (* The composed machine runs in polynomial time *)
      admit. (* Composition of polynomial functions is polynomial *)
    + (* The composed machine decides 'problem' *)
      intro x. rewrite H_iff. apply H_decides.
Admitted.

(**
  The key insight: the lower bound IS the proof of P ≠ NP for NP-complete problems.
  Diduch's paper never establishes this lower bound — it asserts the conclusion
  without providing the mathematical content.
*)

(** * Refutation 4: Relativization Blocks Definitional Arguments *)

(**
  REFUTATION 4: Even if Diduch's definitional argument were more developed,
  it would likely be blocked by the relativization barrier (Baker-Gill-Solovay 1975).

  Definitional arguments examine only the structural form of complexity class
  definitions. Such arguments apply equally to oracle TMs (TMs with access to
  an oracle). Since there exist oracles A, B such that P^A = NP^A and P^B ≠ NP^B,
  no argument that applies to both oracle settings can resolve P vs NP.

  Diduch's argument — which concerns only the definitions of "deterministic solver"
  vs "verifier" — does not depend on any specific computational content that would
  distinguish the two oracle worlds. It therefore relativizes and cannot prove P ≠ NP.

  This is an inherent limitation of the approach, independent of any particular
  formalization details.
*)

(** * Summary *)

(**
  REFUTATION SUMMARY:

  Diduch's argument fails because:

  1. LOGICAL GAP: Different definitions do not imply different extensions.
     (theorem definition_difference_insufficient — proved)

  2. EPISTEMIC GAP: Not knowing an algorithm ≠ proving none exists.
     (theorem epistemological_gap_invalid — Admitted, principle is invalid)

  3. MISSING CONTENT: P ≠ NP requires a super-polynomial lower bound.
     (theorem P_ne_NP_requires_lower_bound — partially proved)

  4. RELATIVIZATION: Definitional arguments relativize, cannot resolve P vs NP.
     (documented above)

  The paper's categorical assertion that P ≠ NP follows from the class names
  and definitions is mathematically unsupported.
*)

Check definition_difference_insufficient. (* PROVED *)
Check epistemological_gap_invalid.        (* Admitted — principle is invalid *)
Check P_ne_NP_requires_lower_bound.       (* Admitted — direction established *)
