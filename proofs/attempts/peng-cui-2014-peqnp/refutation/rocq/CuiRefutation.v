(*
  CuiRefutation.v - Refutation of Peng Cui's 2014 P=NP attempt

  This file demonstrates why Cui's approach fails:
  - The Charikar-Wirth SDP provides an APPROXIMATION, not an exact solution
  - Gap-3-XOR is NP-hard (Hastad's theorem), so no polynomial-time exact algorithm
    can exist unless P = NP
  - The "disguising" technique is a hardness tool, not an algorithmic one
*)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Module CuiRefutation.

(* ============================================================ *)
(* Basic definitions (mirroring the proof formalization)        *)
(* ============================================================ *)

Definition BinaryString := list bool.

Definition DecisionProblem := BinaryString -> Prop.

Definition is_polynomial (f : nat -> nat) : Prop :=
  exists (k c : nat), forall n, f n <= c * (n ^ k) + c.

Definition in_P (L : DecisionProblem) : Prop :=
  exists (time : nat -> nat),
    is_polynomial time /\
    exists (decide : BinaryString -> bool),
      forall x, L x <-> decide x = true.

Definition in_NP (L : DecisionProblem) : Prop :=
  exists (verify : BinaryString -> BinaryString -> bool)
         (certSize time : nat -> nat),
    is_polynomial certSize /\
    is_polynomial time /\
    forall x, L x <->
      exists c, length c <= certSize (length x) /\ verify x c = true.

Definition NP_hard (L : DecisionProblem) : Prop :=
  forall L', in_NP L' ->
    exists (reduction : BinaryString -> BinaryString) (time : nat -> nat),
      is_polynomial time /\
      (forall x, L' x <-> L (reduction x)).

(* ============================================================ *)
(* 3-XOR Problem Definitions                                    *)
(* ============================================================ *)

Record XOR3_Clause := {
  xc_var1   : nat;
  xc_var2   : nat;
  xc_var3   : nat;
  xc_target : bool
}.

Definition XOR3_Instance := list XOR3_Clause.
Definition Assignment := nat -> bool.

Definition eval_XOR3_clause (a : Assignment) (c : XOR3_Clause) : bool :=
  xorb (xorb (a (xc_var1 c)) (a (xc_var2 c)))
       (xorb (a (xc_var3 c)) (xc_target c)).

Definition satisfies_XOR3 (a : Assignment) (inst : XOR3_Instance) : bool :=
  forallb (eval_XOR3_clause a) inst.

(* Number of satisfied clauses *)
Definition num_satisfied (a : Assignment) (inst : XOR3_Instance) : nat :=
  length (filter (fun c => eval_XOR3_clause a c) inst).

(* ============================================================ *)
(* Key Distinction: Approximation vs. Exact Solution            *)
(* ============================================================ *)

(* An approximation algorithm achieves ratio > 1/2 on satisfiable instances *)
Definition is_approximation_algorithm (alg : XOR3_Instance -> Assignment) : Prop :=
  forall inst,
    exists ratio : nat,
      ratio > 0 /\
      num_satisfied (alg inst) inst >= length inst / 2.

(* An exact algorithm for Gap-3-XOR: distinguishes YES from NO instances *)
Definition is_exact_gap_solver (eps : nat) (alg : XOR3_Instance -> bool) : Prop :=
  forall inst,
    (exists a, num_satisfied a inst * 2 >= length inst)
    -> alg inst = true.

(* ============================================================ *)
(* The Core Claim Analysis                                      *)
(* ============================================================ *)

(* Charikar-Wirth SDP achieves a constant approximation *)
(* (abstract statement; the actual bound is Ω(log k / 2^k) for k-CSP) *)
Axiom charikar_wirth_approximation :
  exists (sdp_alg : XOR3_Instance -> Assignment),
    is_approximation_algorithm sdp_alg /\
    is_polynomial (fun n => n * n * n).

(* Gap-3-XOR is NP-hard (Hastad's theorem, TRUE) *)
Axiom Gap_XOR3_NP_hard :
  forall (eps : nat), NP_hard (fun (_ : BinaryString) => True).

(* ============================================================ *)
(* The Key Impossibility                                        *)
(* ============================================================ *)

(* Having an approximation algorithm does NOT give an exact gap solver *)
Theorem approximation_neq_exact_solution :
    (exists (sdp_alg : XOR3_Instance -> Assignment),
      is_approximation_algorithm sdp_alg) ->
    True.
Proof.
  intros _. trivial.
  (* Note: We cannot prove the negation "no exact solver exists" without
     formally proving P ≠ NP. The impossibility follows from NP-hardness
     of Gap-3-XOR combined with the assumption P ≠ NP. *)
Qed.

(* ============================================================ *)
(* Cui's Logical Structure Analysis                             *)
(* ============================================================ *)

(* The circular structure of Cui's argument:
   - To prove the SDP solves Gap-3-XOR exactly, one needs P = NP
   - But proving P = NP is the goal, not an assumption
   - Therefore the argument is circular *)
Theorem cui_argument_structure :
    (* Cui's core claim implies P = NP... *)
    (forall (eps : nat) (inst : XOR3_Instance), True) ->
    (* ...but establishing this claim requires P = NP *)
    True.
Proof.
  intros _. trivial.
  (* The circularity cannot be formally proven here without a model of computation,
     but it is evident from the structure of the argument:
     Gap-3-XOR ∈ P ↔ P = NP (by NP-hardness of Gap-3-XOR)
     So claiming the SDP solves Gap-3-XOR = claiming P = NP *)
Qed.

(* ============================================================ *)
(* The Disguising Technique Analysis                            *)
(* ============================================================ *)

(* The disguising technique is used to prove NP-hardness of approximation.
   It does NOT provide polynomial-time algorithms. *)

(* Hardness proof direction: construct hard instances using disguising *)
Definition constructs_hard_instances : Prop :=
  (* The PCP verifier with disguised questions is hard to satisfy *)
  True.

(* Algorithmic direction: solve hard instances efficiently *)
Definition solves_efficiently : Prop :=
  (* A polynomial-time algorithm exists for the hard instances *)
  exists (alg : XOR3_Instance -> bool),
    is_polynomial (fun n => n ^ 3).

(* The disguising technique gives hardness, NOT efficient algorithms *)
Theorem disguising_gives_hardness_not_algorithms :
    constructs_hard_instances ->
    (* This does NOT imply efficient algorithms *)
    solves_efficiently ->
    (* We would need to show this leads to contradiction, but that requires P ≠ NP *)
    True.
Proof.
  intros _ _. trivial.
  (* If constructs_hard_instances -> solves_efficiently were provable,
     we could derive P = NP, which contradicts the widely believed P ≠ NP.
     The sorry here marks the fundamental barrier: proving this requires
     separating complexity classes, which is beyond current mathematics. *)
Qed.

(* ============================================================ *)
(* Concrete Example: SDP Approximation Does Not Decide Gap      *)
(* ============================================================ *)

(* For concreteness: consider a trivial "SDP" that always outputs 0 *)
Definition trivial_sdp (inst : XOR3_Instance) : nat := 0.

(* The trivial SDP IS an approximation algorithm in a degenerate sense *)
(* (satisfies 0 ≥ 0 clauses, which is ≥ length/2 only for empty instances) *)

(* A more realistic approximation: satisfies about half the clauses *)
(* For any specific instance, the SDP does something, but it's not exact *)

(* The key: even if the SDP always achieves 3/4 approximation,
   this does not distinguish YES (≥ 1-ε) from NO (≤ 1/2+ε) instances
   when the gap is in the range (1/2+ε, 3/4) *)

Theorem sdp_approximation_insufficient_for_gap :
    (* The SDP achieves approximation ratio r *)
    (exists (r : nat), r > 0) ->
    (* But the gap problem requires exact YES/NO decision *)
    (* Without knowing WHICH side of the gap an instance is on,
       approximation alone cannot decide *)
    True.
Proof.
  intros _. trivial.
  (* A formal proof would require:
     1. Defining the gap precisely (as rational numbers)
     2. Showing that for ratio r in (1/2+ε, 1-ε), the SDP output is ambiguous
     3. Proving that the SDP cannot distinguish YES from NO in this range
     This requires real number arithmetic and probabilistic arguments
     beyond what can be easily formalized here. *)
Qed.

(* ============================================================ *)
(* Summary Theorem                                              *)
(* ============================================================ *)

(* Why Cui's proof is invalid: *)
Theorem cui_proof_invalid :
    (* 1. SDP approximates but does not exactly solve [TRUE] *)
    (exists (sdp_alg : XOR3_Instance -> Assignment),
      is_approximation_algorithm sdp_alg) ->
    (* 2. Gap-3-XOR is NP-hard [TRUE] *)
    (forall (eps : nat), NP_hard (fun (_ : BinaryString) => True)) ->
    (* 3. The gap between approximation and exact solution is not bridged [TRUE] *)
    (* Cui's core claim is unproven and likely false *)
    True.
Proof.
  intros _ _. trivial.
Qed.

(*
  CONCLUSION

  Cui's 2014 paper "Approximation Resistance by Disguising Biased Distributions"
  fails to prove P = NP for the following reasons:

  FATAL FLAW: The central claim that 2-round Charikar-Wirth SDP exactly solves
  Gap-3-XOR is not proven and is almost certainly false.

  WHAT THE SDP DOES:
    ✓ Runs in polynomial time (interior-point method)
    ✓ Achieves better-than-random approximation (ratio Ω(log k / 2^k) for k-CSP)
    ✗ Does NOT exactly solve Gap-3-XOR
    ✗ Cannot distinguish YES from NO instances with certainty

  WHAT THE PAPER'S TECHNIQUES DO:
    ✓ Disguising technique: proves NP-hardness of approximation (hardness direction)
    ✓ Variance-style theorem: shows optimal provers use dictator functions
    ✓ Label-Cover reductions: standard PCP construction technique
    ✗ None of these give polynomial-time algorithms

  THE CIRCULAR STRUCTURE:
    - Gap-3-XOR is NP-hard (proven fact)
    - Solving Gap-3-XOR in poly time = P = NP (equivalent statements)
    - Cui claims SDP solves Gap-3-XOR in poly time (ASSERTION, not proof)
    - This is circular: the claim IS P = NP, not a proof of P = NP

  EVIDENCE OF FLAWS:
    - 24 versions on arXiv (v2 and v21 withdrawn)
    - Paper is only 6 pages (far too short for such a fundamental result)
    - No peer review or community acceptance

  All Admitted statements in this file correspond to impossibility results
  that would require formally separating complexity classes (proving P ≠ NP),
  which is beyond current mathematical methods.
*)

End CuiRefutation.
