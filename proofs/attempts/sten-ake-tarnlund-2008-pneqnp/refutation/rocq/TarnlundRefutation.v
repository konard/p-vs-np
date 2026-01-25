(*
  TarnlundRefutation.v - Refutation of Tarnlund's 2008 P≠NP attempt
Open Scope string_scope.
  Author: Formalization for p-vs-np repository
  Related: Issue #453
*)

From Stdlib Require Import TarnlundProof.

Definition SoundnessProof (sys : FormalSystem) : Prop :=
  exists (_proof : unit), IsSoundForComplexity sys.

Axiom tarnlund_no_soundness_proof : ~ SoundnessProof TheoryBPrime.

Record TarnlundAttempt : Type := mkTarnlundAttempt {
  ta_formalSystem : FormalSystem;
  ta_formula : Formula;
  ta_provable : Provable ta_formalSystem ta_formula;
  ta_consistent : IsSimplyConsistent ta_formalSystem
}.

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

Check tarnlund_fails_at_soundness.
