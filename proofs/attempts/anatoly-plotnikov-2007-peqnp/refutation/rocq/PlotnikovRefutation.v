(** Audit of Plotnikov's 2007 P=NP argument. The predicates below name the
    mathematical obligations in the paper; they do not implement its algorithm.
    No missing obligation is introduced as an axiom. *)

Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Module PlotnikovRefutation.

Definition TimeComplexity := nat -> nat.

Definition isPolynomial (T : TimeComplexity) : Prop :=
  exists (c k : nat), forall n : nat, T n <= c * n ^ k.

(** An instance represents a VS-digraph and its initiating set V⁰. The graph,
    fictitious-arc type, and induced set size remain abstract; a full audit
    must link them to an implementation of the paper's construction. *)
Record VSInstance := {
  initialSize : nat;
  largerIndependentSet : Prop;
  FictitiousArc : Type;
  inducedSize : FictitiousArc -> nat
}.

Definition QualifyingArc (i : VSInstance) : Prop :=
  exists arc : FictitiousArc i, inducedSize i arc >= initialSize i - 1.

Definition Conjecture1 (validInstance : VSInstance -> Prop) : Prop :=
  forall i : VSInstance, validInstance i -> largerIndependentSet i -> QualifyingArc i.

(** Graph is an input graph, inLn restricts it to the paper's graph class Lₙ,
    and findsMMIS says that the proposed algorithm returns a maximum
    independent set. None of these predicates is established here. *)
Definition AlgorithmCorrect (Graph : Type) (inLn findsMMIS : Graph -> Prop) : Prop :=
  forall g : Graph, inLn g -> findsMMIS g.

(** Theorem 5 has the form Conjecture 1 -> algorithm correctness. Both the
    implication and Conjecture 1 are explicit proof obligations. *)
Theorem correctness_if_conjecture
    (Graph : Type)
    (validInstance : VSInstance -> Prop)
    (inLn findsMMIS : Graph -> Prop)
    (theorem5 : Conjecture1 validInstance -> AlgorithmCorrect Graph inLn findsMMIS)
    (conjecture1 : Conjecture1 validInstance) :
    AlgorithmCorrect Graph inLn findsMMIS.
Proof.
  exact (theorem5 conjecture1).
Qed.

(** Failure to prove the conjecture cannot refute algorithm correctness. *)
Theorem missing_conjecture_does_not_refute_algorithm :
    ~ (forall C A : Prop, (C -> A) -> ~ C -> ~ A).
Proof.
  intro h.
  assert (implication : False -> True) by (intro f; contradiction).
  assert (not_false : ~ False) by (intro f; exact f).
  exact (h False True implication not_false I).
Qed.

(** An assumption of correctness only yields that same assumption. *)
Theorem identity_implication (P : Prop) : P -> P.
Proof.
  intros h. exact h.
Qed.

Theorem identity_does_not_establish_claim :
    ~ (forall P : Prop, (P -> P) -> P).
Proof.
  intro h. exact (h False (identity_implication False)).
Qed.

(** A polynomial running-time conclusion needs a bound on that running time.
    An unproved correctness conjecture alone supplies no such bound. *)
Theorem polynomial_time_if_bound (T : TimeComplexity)
    (bound : forall n : nat, T n <= n ^ 8) : isPolynomial T.
Proof.
  exists 1, 8. intro n. rewrite Nat.mul_1_l. exact (bound n).
Qed.

(** The old refutation negated polynomiality of this cubic function. *)
Theorem cubic_is_polynomial : isPolynomial (fun n => n * n * n).
Proof.
  exists 1, 3. intro n. simpl. nia.
Qed.

End PlotnikovRefutation.
