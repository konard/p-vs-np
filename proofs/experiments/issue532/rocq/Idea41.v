From Stdlib Require Import List Arith Lia.
From proofs.experiments.issue532.rocq Require Export Idea41Core.
From proofs.experiments.issue532.rocq Require Import CircuitVerifier.
Import Complexity Machines Circuits.
Include Idea41Core.

(** A finite verifier establishes unconditional circuit satisfiability in NP. *)
Theorem circuitSATInNP : CircuitSATInNP.
Proof.
  apply (circuitSATInNP_of_verifier_run CircuitVerifier.candidate
    {| coefficient := 1024 * 6^3; degree := 3 |}).
  intros x cert _. destruct (CircuitVerifier.verifier_run x cert) as [t [ht hr]].
  exists t. split; [|exact hr]. apply Nat.le_trans with (1 := ht).
  unfold evalPoly. cbn [coefficient degree].
  replace (length x + length cert + 1 + 1) with (length x + length cert + 2) by lia.
  apply Nat.le_trans with (1024 * (6 * (length x + length cert + 2))^3).
  - apply Nat.mul_le_mono_l, Nat.pow_le_mono_l. lia.
  - rewrite Nat.pow_mul_l, Nat.mul_assoc. reflexivity.
Qed.

(** P = NP implies the obligation. *)
Theorem fastCircuitSAT_of_pEqualsNP : PEqualsNP -> FastCircuitSAT.
Proof. intros h. exact (fastCircuitSAT_of_inP (h CircuitSAT circuitSATInNP)). Qed.

(** A polynomial-time SAT decider implies the obligation, given
    Cook-Levin. *)
Theorem fastCircuitSAT_of_inP_sat : SATHard -> InP SAT -> FastCircuitSAT.
Proof.
  intros hard h. exact (fastCircuitSAT_of_pEqualsNP (pEqualsNP_of_inP_sat hard h)).
Qed.

(** Bridge.  Refuting the obligation proves P <> NP. *)
Theorem pNotEqualsNP_of_not_fastCircuitSAT : ~ FastCircuitSAT ->
  PNotEqualsNP.
Proof. intros h hEq. exact (h (fastCircuitSAT_of_pEqualsNP hEq)). Qed.

(** "NEXP is contained in P/poly" would prove P <> NP, given the known
    theorems. *)
Theorem pNotEqualsNP_of_nexpSubsetPPoly : NTimeHierarchy ->
  EasyWitnessLemma -> WilliamsSpeedup -> NEXPSubsetPPoly -> PNotEqualsNP.
Proof.
  intros hier ewl speedup hsub.
  exact (pNotEqualsNP_of_not_fastCircuitSAT
    (not_fastCircuitSAT_of_nexpSubsetPPoly hier ewl speedup hsub)).
Qed.

(** P = NP would refute "NEXP is contained in P/poly", given the known
    theorems. *)
Theorem not_nexpSubsetPPoly_of_pEqualsNP : NTimeHierarchy ->
  EasyWitnessLemma -> WilliamsSpeedup -> PEqualsNP -> ~ NEXPSubsetPPoly.
Proof.
  intros hier ewl speedup h.
  exact (williams_method hier ewl speedup (fastCircuitSAT_of_pEqualsNP h)).
Qed.
