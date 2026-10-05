(** * Issue 10: the Williams route to NP not contained in P, over the shared model

    The Rocq twin of [proofs/experiments/issue10/lean/NPNotSubsetP.lean],
    with the same statement names.  Every cost is a number of [Run] steps of a
    finite-table [Machine]; circuits are the shared gate lists, whose length
    is the size and whose semantics is [output].  The algorithm-to-lower-bound
    direction is Idea 41 ([williams_method]).  Known theorems are hypotheses;
    nothing is assumed as an axiom.  The next ingredient to discharge is
    [CircuitSATInNP], the circuit-evaluating verifier;
    [satisfying_input_within_certBound] is its certificate-length half. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits Idea41.

(** ** The target: NP not contained in P *)

Definition NPNotSubsetP : Prop := ~ (forall L : Language, InNP L -> InP L).

(** The shared statement [PNotEqualsNP] is literally NP not contained in P. *)
Theorem npNotSubsetP_iff_pNotEqualsNP : NPNotSubsetP <-> PNotEqualsNP.
Proof. reflexivity. Qed.

(** Because P is contained in NP, NP not contained in P says exactly that the
    classes differ. *)
Theorem npNotSubsetP_iff_classes_differ :
  NPNotSubsetP <-> ~ (forall L : Language, InP L <-> InNP L).
Proof.
  split.
  - intros h heq. apply h. intros L hL. apply (heq L). exact hL.
  - intros h hsub. apply h. intro L. split; [apply pSubsetNP | apply hsub].
Qed.

Theorem npNotSubsetP_of_witness : forall L : Language, InNP L -> ~ InP L -> NPNotSubsetP.
Proof. intros L hnp hp h. exact (hp (h L hnp)). Qed.

(** With excluded middle, NP not contained in P gives a witness. *)
Theorem witness_of_npNotSubsetP : (forall P : Prop, P \/ ~ P) -> NPNotSubsetP ->
  exists L : Language, InNP L /\ ~ InP L.
Proof.
  intros em h. destruct (em (exists L : Language, InNP L /\ ~ InP L)) as [hw | hw];
    [exact hw |].
  exfalso. apply h. intros L hL. destruct (em (InP L)) as [hp | hp]; [exact hp |].
  exfalso. exact (hw (ex_intro _ L (conj hL hp))).
Qed.

(** ** Reproducing the PR #43 defects *)

Module Legacy.

(** Size, depth and semantics are independent fields. *)
Record Circuit := {
  size : nat;
  depth : nat;
  numInputs : nat;
  compute : (nat -> bool) -> bool
}.

Definition ACC0 (C : Circuit) : Prop := depth C <= 10.

Definition PPoly (C : Circuit) : Prop := exists k : nat, size C <= numInputs C ^ k.

(** The running time is a free function next to the answer. *)
Record SATAlgorithm := {
  solve : Circuit -> bool;
  timeComplexity : nat -> nat
}.

Definition IsFastSATAlgorithm (alg : SATAlgorithm) : Prop :=
  exists delta : nat, delta > 0 /\ forall n : nat, timeComplexity alg n <= 2 ^ n - n ^ delta.

End Legacy.

(** Any function on any number of inputs is a zero-gate, depth-zero legacy
    circuit in both classes. *)
Theorem legacy_every_function_small : forall (n : nat) (f : (nat -> bool) -> bool),
  Legacy.ACC0 {| Legacy.size := 0; Legacy.depth := 0; Legacy.numInputs := n;
                 Legacy.compute := f |} /\
  Legacy.PPoly {| Legacy.size := 0; Legacy.depth := 0; Legacy.numInputs := n;
                  Legacy.compute := f |}.
Proof.
  intros n f. split; [unfold Legacy.ACC0; simpl; lia |].
  exists 0. simpl. lia.
Qed.

(** Any legacy solver is "fast" once its cost label is set to zero. *)
Theorem legacy_zero_cost_is_fast : forall solve : Legacy.Circuit -> bool,
  Legacy.IsFastSATAlgorithm {| Legacy.solve := solve; Legacy.timeComplexity := fun _ => 0 |}.
Proof. intro solve. exists 1. split; [lia |]. intro n. simpl. lia. Qed.

(** [2^n - n^delta] is not [2^(n - n^delta)]. *)
Theorem legacy_bound_misread : 2 ^ 4 - 4 ^ 1 <> 2 ^ (4 - 4 ^ 1).
Proof. simpl. discriminate. Qed.

(** With [delta : nat], the exponent [n - n^delta] truncates to zero. *)
Theorem legacy_exponent_collapses : forall delta n, 1 <= delta -> 2 ^ (n - n ^ delta) = 1.
Proof.
  intros delta n hd. destruct n as [| n].
  - simpl. reflexivity.
  - assert (h : S n <= S n ^ delta).
    { rewrite <- (Nat.pow_1_r (S n)) at 1. apply Nat.pow_le_mono_r; lia. }
    replace (S n - S n ^ delta) with 0 by lia. reflexivity.
Qed.

(** The legacy bound saves only a polynomial amount and breaks the Williams
    budget [t * (n+1) <= 2^n] at [c = 1] on arbitrarily large lengths. *)
Theorem legacy_bound_misses_budget : forall delta n0,
  exists n, n0 <= n /\ 2 ^ n < (2 ^ n - n ^ delta) * (n + 1) ^ 1.
Proof.
  intros delta n0. destruct (poly_le_two_pow 2 delta) as [N hN].
  exists (n0 + N + 2). split; [lia |].
  set (n := n0 + N + 2).
  pose proof (hN n ltac:(unfold n; lia)) as hb.
  assert (hp : n ^ delta <= (n + 1) ^ delta) by (apply Nat.pow_le_mono_l; lia).
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as hpos.
  rewrite Nat.pow_1_r.
  apply Nat.lt_le_trans with ((2 ^ n - n ^ delta) * 3); [lia |].
  apply Nat.mul_le_mono_l. unfold n. lia.
Qed.

(** ** Negative tests for the shared model *)

(** No run costs zero steps. *)
Theorem run_pos : forall m c t b, Run m c t b -> 0 < t.
Proof. intros m c t b h. destruct h; lia. Qed.

(** A one-step run is a halting instruction. *)
Theorem step_of_run_one : forall m c t b, Run m c t b -> t = 1 -> step m c = inl b.
Proof.
  intros m c t b h ht. destruct h as [c b hs | c c' t b hs hr]; [exact hs |].
  pose proof (run_pos _ _ _ _ hr). lia.
Qed.

(** A halting step reads only the state and the scanned symbol. *)
Theorem step_halt_congr : forall m c c' b,
  state c = state c' -> tapeHead c = tapeHead c' -> step m c = inl b -> step m c' = inl b.
Proof.
  intros m c c' b hs hh h. unfold step in *. rewrite <- hs, <- hh.
  destruct (instruction m (state c) (tapeHead c)); [exact h | discriminate].
Qed.

(** The constant-true and constant-false circuits on one input. *)
Definition oneTrue : Circuit := [(0, 0); (0, 1)].
Definition oneFalse : Circuit := [(0, 0); (0, 1); (2, 2)].

Theorem wf_oneTrue : WF 1 oneTrue.
Proof. unfold WF, oneTrue. simpl. repeat split; lia. Qed.

Theorem wf_oneFalse : WF 1 oneFalse.
Proof. unfold WF, oneFalse. simpl. repeat split; lia. Qed.

Theorem satisfiable_oneTrue : CircuitSatisfiable 1 oneTrue.
Proof. exists [false]. split; reflexivity. Qed.

Theorem unsatisfiable_oneFalse : ~ CircuitSatisfiable 1 oneFalse.
Proof.
  intros [x [hx ho]].
  destruct x as [| a [| y x]]; try discriminate hx.
  destruct a; discriminate ho.
Qed.

(** No machine decides satisfiability of well-formed circuits in one step. *)
Theorem no_one_step_circuitSAT : forall m : Machine,
  ~ (forall n C, WF n C -> exists b, Run m (initial (encCircuit n C)) 1 b /\
       (b = true <-> CircuitSatisfiable n C)).
Proof.
  intros m h.
  destruct (h 1 oneTrue wf_oneTrue) as [b [hr hb]].
  destruct (h 1 oneFalse wf_oneFalse) as [b' [hr' hb']].
  pose proof (step_halt_congr m (initial (encCircuit 1 oneTrue))
                (initial (encCircuit 1 oneFalse)) b eq_refl eq_refl
                (step_of_run_one _ _ _ _ hr eq_refl)) as hs.
  rewrite (step_of_run_one _ _ _ _ hr' eq_refl) in hs.
  injection hs as e. subst b'.
  exact (unsatisfiable_oneFalse (proj1 hb' (proj2 hb satisfiable_oneTrue))).
Qed.

(** A gate that reads a wire that does not exist yet is malformed. *)
Theorem malformed_forward_wire : ~ WF 1 [(0, 1)].
Proof. unfold WF. simpl. lia. Qed.

(** A gate on zero inputs is malformed. *)
Theorem malformed_no_inputs : ~ WF 0 [(0, 0)].
Proof. unfold WF. simpl. lia. Qed.

(** The malformed circuit [[(0,1)]] outputs [true], yet [CircuitSAT] rejects
    it. *)
Theorem malformed_rejected :
  CircuitSatisfiable 1 [(0, 1)] /\ CircuitSAT (encCircuit 1 [(0, 1)]) = false.
Proof.
  split; [exists [false]; split; reflexivity |].
  destruct (CircuitSAT (encCircuit 1 [(0, 1)])) eqn:h; [| reflexivity].
  exfalso. exact (malformed_forward_wire (proj1 (proj1 (circuitSAT_encode 1 [(0, 1)]) h))).
Qed.

(** ** The Williams budget is not polynomial *)

(** [2^n / (n+1)^c] is not polynomially bounded, so meeting [FastCircuitSAT]
    does not require P = NP; [fastCircuitSAT_of_inP] is the converse. *)
Theorem williams_budget_not_polynomial : forall c : nat,
  ~ PolynomiallyBounded (fun n => 2 ^ n / (n + 1) ^ c).
Proof.
  intros c [a [k h]].
  destruct (poly_le_two_pow (2 * (a + 1)) (k + c)) as [N hN].
  pose proof (h N) as hd. simpl in hd.
  assert (hq : (N + 1) ^ c <> 0) by (apply Nat.pow_nonzero; lia).
  assert (hk : 1 <= (N + 1) ^ k) by (apply Nat.le_trans with (1 ^ k);
    [rewrite Nat.pow_1_l; lia | apply Nat.pow_le_mono_l; lia]).
  pose proof (Nat.div_mod (2 ^ N) ((N + 1) ^ c) hq) as hdm.
  pose proof (Nat.mod_upper_bound (2 ^ N) ((N + 1) ^ c) hq) as hmod.
  pose proof (hN N (le_n N)) as hb.
  rewrite Nat.pow_add_r in hb.
  set (P := (N + 1) ^ k) in *. set (Q := (N + 1) ^ c) in *.
  set (D := 2 ^ N / Q) in *. set (R := 2 ^ N mod Q) in *.
  assert (h1 : Q * D <= Q * (a * P)) by (apply Nat.mul_le_mono_l; exact hd).
  assert (h2 : Q * (a * P) + Q <= (a + 1) * (P * Q)) by nia.
  lia.
Qed.

(** ** The enumeration diagonal fails *)

(** On every input of positive length, for every bit, a well-formed circuit
    with at most three gates outputs that bit. *)
Theorem constant_circuit_agrees : forall (x : Word) (b : bool), 0 < length x ->
  exists C : Circuit, WF (length x) C /\ length C <= 3 /\ output x C = b.
Proof.
  intros x b hx. destruct b.
  - exists [(0, 0); (0, length x)]. split; [unfold WF; simpl; repeat split; lia |].
    split; [simpl; lia | exact (output_const_true x hx)].
  - exists [(0, 0); (0, length x); (length x + 1, length x + 1)].
    split; [unfold WF; simpl; repeat split; lia |].
    split; [simpl; lia | exact (output_const_false x hx)].
Qed.

Theorem no_bit_differs_from_all_circuits : forall (x : Word) (b : bool), 0 < length x ->
  ~ (forall C : Circuit, WF (length x) C -> length C <= 3 -> output x C <> b).
Proof.
  intros x b hx h. destruct (constant_circuit_agrees x b hx) as [C [hw [hl ho]]].
  exact (h C hw hl ho).
Qed.

(** ** The corrected bridges *)

Definition NPSubsetPPoly : Prop := forall L : Language, InNP L -> InPPoly L.

(** The PR #43 bridge, using the proved inclusion [pSubsetPPoly]. *)
Theorem npNotSubsetP_of_not_npSubsetPPoly : ~ NPSubsetPPoly -> NPNotSubsetP.
Proof. intros h hsub. apply h. intros L hL. exact (pSubsetPPoly L (hsub L hL)). Qed.

(** Williams' method yields NEXP not contained in P/poly, not the NP
    statement. *)
Theorem williams_nexp_lower_bound : NTimeHierarchy -> EasyWitnessLemma -> WilliamsSpeedup ->
  FastCircuitSAT -> ~ NEXPSubsetPPoly.
Proof. exact williams_method. Qed.

(** NEXP not contained in P/poly also follows from P = NP under the same
    theorems. *)
Theorem nexp_lower_bound_of_pEqualsNP : CircuitSATInNP -> NTimeHierarchy ->
  EasyWitnessLemma -> WilliamsSpeedup -> PEqualsNP -> ~ NEXPSubsetPPoly.
Proof. exact not_nexpSubsetPPoly_of_pEqualsNP. Qed.

(** The route that does reach NP not contained in P. *)
Theorem npNotSubsetP_of_not_fastCircuitSAT : CircuitSATInNP -> ~ FastCircuitSAT ->
  NPNotSubsetP.
Proof. exact pNotEqualsNP_of_not_fastCircuitSAT. Qed.

(** ** The next ingredient: [CircuitSATInNP]

    The certificate is a satisfying input of [n] bits; the encoding starts
    with [n + 1] bits.  The remaining part is the evaluating [Machine]. *)
Theorem satisfying_input_within_certBound : forall n C, CircuitSatisfiable n C ->
  exists x : Word, length x <= evalPoly {| coefficient := 1; degree := 1 |}
                                 (length (encCircuit n C)) /\ output x C = true.
Proof.
  intros n C [x [hx ho]]. exists x. split; [| exact ho].
  unfold evalPoly, encCircuit. simpl. rewrite length_app, length_encNat. lia.
Qed.
