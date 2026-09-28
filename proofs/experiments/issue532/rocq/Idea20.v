(* Issue #532, Idea 20: parallel and physical cost models.

   Rocq counterpart of lean/Idea20.lean.  A schedule is a list of rounds of
   task identifiers.  Proves: W distinct tasks on p processors need
   W <= p * rounds (rounds_lower_bound); a chain of length d needs d rounds
   (span_bound); sequential simulation costs at most p * rounds, so
   polynomial processors and rounds give polynomial work (abstract NC in P,
   poly_parallel_in_poly_sequential); 2^n tasks cannot be covered with
   polynomial processors in polynomially many rounds for large n
   (poly_parallel_cannot_hide_exponential_work); an abstract physical run
   obeys the same bound iff it is resource honest (physical_conditional,
   dishonest_model_collapses).  The physical postulate is the generic
   schema PhysicalResourceHonestyFor over a free predicate Realizable; its
   instance for machine deciders of the shared model is proved
   (physicalResourceHonesty_machine), and such a run does not perform 2^n
   work (machine_run_not_exponential).  Verdict: refuted as a route.

   Differences from Lean: none in the statements.  Record equality
   R = machinePhysicalRun p is eliminated with subst. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(* ---------- Schedules ---------- *)

Definition Schedule := list (list nat).

Fixpoint flat (s : Schedule) : list nat :=
  match s with
  | [] => []
  | r :: s' => r ++ flat s'
  end.

Fixpoint totalWork (s : Schedule) : nat :=
  match s with
  | [] => 0
  | r :: s' => length r + totalWork s'
  end.

Lemma length_flat : forall s, length (flat s) = totalWork s.
Proof.
  induction s as [|r s IH]; simpl; auto. rewrite length_app, IH. reflexivity.
Qed.

Lemma mem_flat : forall s t, In t (flat s) <-> exists r, In r s /\ In t r.
Proof.
  induction s as [|r s IH]; intros t; simpl.
  - split; [intros [] | intros [r [[] _]]].
  - rewrite in_app_iff, IH. split.
    + intros [H | [r' [Hr' Ht]]]; [exists r | exists r']; auto.
    + intros [r' [[Hr' | Hr'] Ht]]; [subst; left; auto | right; exists r'; auto].
Qed.

Definition UsesAtMost (p : nat) (s : Schedule) : Prop :=
  forall r, In r s -> length r <= p.

Definition Covers (W : nat) (s : Schedule) : Prop :=
  forall t, t < W -> exists r, In r s /\ In t r.

Theorem work_bound : forall p s, UsesAtMost p s -> totalWork s <= p * length s.
Proof.
  intros p s. induction s as [|r s IH]; intros H; simpl; [lia|].
  assert (Hr : length r <= p) by (apply H; simpl; auto).
  assert (Hs : totalWork s <= p * length s) by (apply IH; intros r' Hr'; apply H; simpl; auto).
  lia.
Qed.

Theorem covers_work : forall W s, Covers W s -> W <= totalWork s.
Proof.
  intros W s H. rewrite <- length_flat.
  replace W with (length (seq 0 W)) by apply length_seq.
  apply NoDup_incl_length; [apply seq_NoDup|].
  intros t Ht. apply in_seq in Ht. apply mem_flat. apply H. lia.
Qed.

Theorem rounds_lower_bound : forall W p s,
  UsesAtMost p s -> Covers W s -> W <= p * length s.
Proof.
  intros W p s Hp HW. pose proof (covers_work W s HW). pose proof (work_bound p s Hp). lia.
Qed.

Theorem span_bound : forall d R (round : nat -> nat),
  (forall i, i + 1 < d -> round i < round (i + 1)) ->
  (forall i, i < d -> round i < R) -> d <= R.
Proof.
  intros d R round Hinc Hlt.
  assert (key : forall i, i < d -> i <= round i).
  { induction i as [|i IH]; intros Hi; [lia|].
    pose proof (IH ltac:(lia)). pose proof (Hinc i ltac:(lia)).
    replace (S i) with (i + 1) by lia. lia. }
  destruct d as [|d]; [lia|].
  pose proof (key d ltac:(lia)). pose proof (Hlt d ltac:(lia)). lia.
Qed.

Theorem brent_lower_bound : forall W p d s (round : nat -> nat),
  UsesAtMost p s -> Covers W s ->
  (forall i, i + 1 < d -> round i < round (i + 1)) ->
  (forall i, i < d -> round i < length s) ->
  W <= p * length s /\ d <= length s.
Proof.
  intros W p d s round Hp HW Hinc Hlt. split.
  - apply rounds_lower_bound; auto.
  - apply (span_bound d (length s) round); auto.
Qed.

(* ---------- Polynomial resources ---------- *)

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

Theorem sequential_simulation : forall p s,
  UsesAtMost p s -> length (flat s) <= p * length s.
Proof. intros p s H. rewrite length_flat. apply work_bound. exact H. Qed.

Lemma polyEval_mul : forall c k c' k' n,
  polyEval c k n * polyEval c' k' n = polyEval (c * c') (k + k') n.
Proof.
  intros. unfold polyEval. rewrite Nat.pow_add_r. ring.
Qed.

Theorem poly_parallel_in_poly_sequential : forall c k c' k' n s,
  UsesAtMost (polyEval c k n) s -> length s <= polyEval c' k' n ->
  totalWork s <= polyEval (c * c') (k + k') n.
Proof.
  intros c k c' k' n s Hp HT.
  pose proof (work_bound _ s Hp) as H1.
  rewrite <- polyEval_mul.
  apply Nat.le_trans with (polyEval c k n * length s); auto.
  apply Nat.mul_le_mono_l. exact HT.
Qed.

Lemma succ_le_two_pow : forall q, q + 1 <= 2 ^ q.
Proof. induction q as [|q IH]; simpl; lia. Qed.

Lemma lt_two_pow_self : forall a, a < 2 ^ a.
Proof. intros a. pose proof (succ_le_two_pow a). lia. Qed.

Theorem linear_lt_exp : forall a q, 2 * a + 1 <= q -> a * (q + 1) < 2 ^ q.
Proof.
  intros a q Hq.
  replace q with (2 * a + 1 + (q - (2 * a + 1))) by lia.
  generalize (q - (2 * a + 1)) as d. clear q Hq.
  induction d as [|d IH].
  - rewrite Nat.add_0_r.
    replace (2 * a + 1) with (a + S a) by lia.
    rewrite Nat.pow_add_r, Nat.pow_succ_r'.
    pose proof (succ_le_two_pow a). pose proof (lt_two_pow_self a).
    nia.
  - replace (2 * a + 1 + S d) with (S (2 * a + 1 + d)) by lia.
    rewrite Nat.pow_succ_r'.
    assert (a <= a * (2 * a + 1 + d + 1)) by nia.
    lia.
Qed.

Theorem dyadic_bracket : forall n, 1 <= n -> exists L, 2 ^ L <= n /\ n < 2 ^ (L + 1).
Proof.
  intros n Hn. replace n with (1 + (n - 1)) by lia.
  generalize (n - 1) as d. clear n Hn.
  induction d as [|d IH].
  - exists 0. simpl. lia.
  - destruct IH as [L [H1 H2]].
    destruct (Nat.lt_ge_cases (1 + S d) (2 ^ (L + 1))) as [H|H].
    + exists L. split; lia.
    + exists (L + 1). split; [lia|].
      replace (L + 1 + 1) with (S (L + 1)) by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

Theorem exp_beats_poly : forall c k n,
  2 ^ (2 * (c + k) + 1) <= n -> polyEval c k n < 2 ^ n.
Proof.
  intros c k n Hn. unfold polyEval.
  assert (Hn1 : 1 <= n).
  { pose proof (Nat.pow_le_mono_r 2 0 (2 * (c + k) + 1) ltac:(lia) ltac:(lia)).
    rewrite Nat.pow_0_r in H. lia. }
  destruct (dyadic_bracket n Hn1) as [L [HL1 HL2]].
  assert (HLbig : 2 * (c + k) + 1 <= L).
  { destruct (Nat.le_gt_cases (2 * (c + k) + 1) L) as [H|H]; auto.
    pose proof (Nat.pow_le_mono_r 2 (L + 1) (2 * (c + k) + 1) ltac:(lia) ltac:(lia)).
    lia. }
  pose proof (linear_lt_exp (c + k) L HLbig) as Hlin.
  assert (Hsum : c + k * (L + 1) < n).
  { assert (c <= c * (L + 1)) by nia.
    rewrite Nat.mul_add_distr_r in Hlin. lia. }
  assert (Hbase : (n + 1) ^ k <= 2 ^ ((L + 1) * k)).
  { rewrite Nat.pow_mul_r. apply Nat.pow_le_mono_l. lia. }
  pose proof (lt_two_pow_self c) as Hc.
  assert (Hpos : 0 < 2 ^ ((L + 1) * k)).
  { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
  apply Nat.le_lt_trans with (c * 2 ^ ((L + 1) * k)).
  { apply Nat.mul_le_mono_l. exact Hbase. }
  apply Nat.lt_le_trans with (2 ^ c * 2 ^ ((L + 1) * k)).
  { apply Nat.mul_lt_mono_pos_r; auto. }
  rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
Qed.

Theorem exp_work_forces_superpoly_processors : forall n p s,
  UsesAtMost p s -> Covers (2 ^ n) s -> 2 ^ n <= p * length s.
Proof. intros n p s Hp HW. apply rounds_lower_bound; auto. Qed.

Theorem poly_parallel_cannot_hide_exponential_work : forall c k c' k' n,
  2 ^ (2 * (c * c' + (k + k')) + 1) <= n ->
  forall s, UsesAtMost (polyEval c k n) s -> Covers (2 ^ n) s ->
    polyEval c' k' n < length s.
Proof.
  intros c k c' k' n Hn s Hp HW.
  destruct (Nat.lt_ge_cases (polyEval c' k' n) (length s)) as [H|H]; auto.
  pose proof (covers_work _ s HW) as H1.
  pose proof (poly_parallel_in_poly_sequential c k c' k' n s Hp H) as H2.
  pose proof (exp_beats_poly (c * c') (k + k') n Hn) as H3.
  lia.
Qed.

(* ---------- Physical models ---------- *)

Record PhysicalRun := {
  work : nat -> nat;
  time : nat -> nat;
  resource : nat -> nat
}.

Definition ResourceHonest (m : PhysicalRun) : Prop :=
  forall n, work m n <= time m n * resource m n.

Theorem schedule_is_honest : forall p s,
  UsesAtMost p s -> totalWork s <= length s * p.
Proof. intros p s H. rewrite Nat.mul_comm. apply work_bound. exact H. Qed.

(** Generic schema over a free physical predicate Realizable: every
    realisable run is resource honest.  Realizable is supplied by physics, so
    this is a postulate and not a statement of complexity theory; its machine
    instance physicalResourceHonesty_machine is proved below. *)
Definition PhysicalResourceHonestyFor (Realizable : PhysicalRun -> Prop) : Prop :=
  forall m, Realizable m -> ResourceHonest m.

Theorem physical_conditional : forall (Realizable : PhysicalRun -> Prop),
  PhysicalResourceHonestyFor Realizable ->
  forall m, Realizable m -> (forall n, work m n = 2 ^ n) ->
  forall c' k', (forall n, time m n <= polyEval c' k' n) ->
  forall c k n, 2 ^ (2 * (c * c' + (k + k')) + 1) <= n ->
    polyEval c k n < resource m n.
Proof.
  intros Realizable Hphys m Hm Hwork c' k' Htime c k n Hn.
  destruct (Nat.lt_ge_cases (polyEval c k n) (resource m n)) as [H|H]; auto.
  pose proof (Hphys m Hm n) as H1. rewrite Hwork in H1.
  assert (H2 : time m n * resource m n <= polyEval c' k' n * polyEval c k n).
  { apply Nat.mul_le_mono; auto. }
  assert (E : polyEval c' k' n * polyEval c k n = polyEval (c * c') (k + k') n).
  { rewrite Nat.mul_comm. apply polyEval_mul. }
  rewrite E in H2.
  pose proof (exp_beats_poly (c * c') (k + k') n Hn) as H3.
  lia.
Qed.

Theorem dishonest_model_collapses :
  exists m : PhysicalRun, (forall n, work m n = 2 ^ n) /\ (forall n, time m n = 1) /\
    (forall n, resource m n = 1) /\ ~ ResourceHonest m.
Proof.
  exists {| work := fun n => 2 ^ n; time := fun _ => 1; resource := fun _ => 1 |}.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros H. specialize (H 1). simpl in H. lia.
Qed.

(* ---------- Machine part: sequential machines as physical runs ---------- *)

(** The physical run of a machine decider clocked by p: work and time are
    both the step bound evalPoly p of Run, on one processor. *)
Definition machinePhysicalRun (p : Polynomial) : PhysicalRun :=
  {| work := evalPoly p; time := evalPoly p; resource := fun _ => 1 |}.

(** The physical runs of polynomial-time machine deciders of the shared model. *)
Definition MachineRealizable (R : PhysicalRun) : Prop :=
  exists (m : Machine) (p : Polynomial) (L : Language),
    DecidesWithin m p L /\ R = machinePhysicalRun p.

(** Machine instance of the schema (proved): runs of machine deciders are
    resource honest with one processor. *)
Theorem physicalResourceHonesty_machine : PhysicalResourceHonestyFor MachineRealizable.
Proof.
  intros R [m [p [L [_ HR]]]] n. subst R. simpl. lia.
Qed.

(** A polynomial-time machine does not perform 2^n work (from exp_beats_poly). *)
Theorem machine_run_not_exponential : forall R : PhysicalRun,
  MachineRealizable R -> ~ (forall n, work R n = 2 ^ n).
Proof.
  intros R [m [p [L [_ HR]]]] H. subst R.
  set (n := 2 ^ (2 * (coefficient p + degree p) + 1)).
  pose proof (exp_beats_poly (coefficient p) (degree p) n (Nat.le_refl _)) as H1.
  specialize (H n). simpl in H. unfold evalPoly in H. unfold polyEval in H1.
  lia.
Qed.
