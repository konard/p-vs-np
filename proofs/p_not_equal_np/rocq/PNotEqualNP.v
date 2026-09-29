(** Conditional P ≠ NP criteria over the shared finite-machine semantics.
    SAT membership and NP-completeness must be supplied as separate proofs. *)
From Stdlib Require Import Classical_Prop.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Definition DecisionProblem := Language.
Definition P_equals_NP : Prop :=
  forall problem : DecisionProblem, InP problem <-> InNP problem.
Definition P_not_equals_NP : Prop := ~ P_equals_NP.

Theorem P_subset_NP : forall problem, InP problem -> InNP problem.
Proof. exact pSubsetNP. Qed.

Theorem test_existence_of_hard_problem :
  P_not_equals_NP <-> exists problem, InNP problem /\ ~ InP problem.
Proof.
  unfold P_not_equals_NP, P_equals_NP.
  split.
  - intro hneq.
    apply NNPP. intro hnone.
    apply hneq. intro problem. split.
    + apply P_subset_NP.
    + intro hnp. apply NNPP. intro hnotp.
      apply hnone. exists problem. split; assumption.
  - intros [problem [hnp hnotp]] heq.
    apply hnotp. apply heq. exact hnp.
Qed.

(** A completeness predicate is an explicit premise. There is no unconnected
    reduction function or claimed SAT theorem in this file. *)
Theorem test_NP_complete_not_in_P :
  forall (IsNPComplete : DecisionProblem -> Prop),
    (forall problem, IsNPComplete problem -> InNP problem) ->
    (exists problem, IsNPComplete problem /\ ~ InP problem) ->
    P_not_equals_NP.
Proof.
  intros complete complete_in_NP [problem [hcomplete hnotp]].
  apply test_existence_of_hard_problem.
  exists problem. split; [apply complete_in_NP; exact hcomplete | exact hnotp].
Qed.

Theorem test_SAT_not_in_P :
  forall (sat : DecisionProblem), InNP sat -> ~ InP sat -> P_not_equals_NP.
Proof.
  intros sat hnp hnotp.
  apply test_existence_of_hard_problem.
  exists sat. split; assumption.
Qed.

Definition HasSuperPolynomialLowerBound (problem : DecisionProblem) : Prop :=
  forall (machine : Machine) (bound : Polynomial),
    ~(forall x, exists t b,
      t <= evalPoly bound (List.length x) /\
      Run machine (initial x) t b /\
      (problem x = true <-> b = true)).

Theorem test_super_polynomial_lower_bound :
  (exists problem, InNP problem /\ HasSuperPolynomialLowerBound problem) ->
  P_not_equals_NP.
Proof.
  intros [problem [hnp hlower]].
  apply test_existence_of_hard_problem.
  exists problem. split; [exact hnp |].
  intros [p hp].
  apply (hlower (p_machine p) (p_bound p)).
  intro x.
  destruct (p_terminates p x) as [t [b [ht hr]]].
  exists t, b. split; [exact ht |]. split; [exact hr |].
  rewrite <- hp. exact (p_correct p x t b hr).
Qed.

Record ProofOfPNotEqualNP := {
  proves : P_not_equals_NP
}.

(** The proof term, rather than this Boolean, is checked by Rocq. *)
Definition verifyPNotEqualNPProof (_proof : ProofOfPNotEqualNP) : bool := true.

Definition checkProblemWitness (problem : DecisionProblem)
    (hnp : InNP problem) (hnotp : ~ InP problem) : ProofOfPNotEqualNP :=
  {| proves :=
      proj2 test_existence_of_hard_problem
        (ex_intro _ problem (conj hnp hnotp)) |}.

Definition checkSATWitness (sat : DecisionProblem)
    (hnp : InNP sat) (hnotp : ~ InP sat) : ProofOfPNotEqualNP :=
  {| proves := test_SAT_not_in_P sat hnp hnotp |}.

Print Assumptions test_existence_of_hard_problem.
