(* Issue #532, Idea 40: size-uniform invariant (induction with resource bounds).

   Rocq counterpart of ../lean/Idea40.lean (same theorem names and content).
   Additive recurrences T(n+1) <= T(n) + q(n) with q monotone give
   T(n) <= c + n * q(n), polynomial when q is (additive_bound, additive_poly);
   doubling/branching recurrences give 2^n (doubling_exact, branching_lower), which
   beats every polynomial (poly_lt_two_pow, branching_not_poly,
   branchCost_exponential). A self-reduction with one same-answer call and
   polynomial step cost gives a correct polynomial-cost solver
   (obligation_gives_poly_solver); AdditiveSelfReduction is the open obligation
   (for SAT it would give P = NP). All proofs are constructive. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.

(* Induction principle for correctness invariants (old tested). *)
Theorem tested (P : nat -> Prop) :
  P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros Hbase Hstep n; induction n.
  - exact Hbase.
  - apply Hstep, IHn.
Qed.

(* (a) Additive recurrences are polynomial. *)

Theorem additive_bound (T q : nat -> nat) (c : nat) :
  T 0 <= c -> (forall n, T (n + 1) <= T n + q n) ->
  (forall m n, m <= n -> q m <= q n) ->
  forall n, T n <= c + n * q n.
Proof.
  intros H0 Hstep Hmono n. induction n as [|n IH].
  - simpl. lia.
  - pose proof (Hstep n) as H1.
    pose proof (Hmono n (n + 1) ltac:(lia)) as H2.
    assert (H3 : n * q n <= n * q (n + 1)) by (apply Nat.mul_le_mono_l; exact H2).
    replace (S n) with (n + 1) by lia.
    rewrite Nat.mul_add_distr_r. lia.
Qed.

Theorem additive_poly_closed (c a k n : nat) :
  c + n * (a * (n + 1) ^ k) <= (c + a) * (n + 1) ^ (k + 1).
Proof.
  assert (Hx : 1 <= (n + 1) ^ (k + 1)).
  { pose proof (Nat.pow_le_mono_l 1 (n + 1) (k + 1) ltac:(lia)) as H.
    rewrite Nat.pow_1_l in H. exact H. }
  assert (H1 : c <= c * (n + 1) ^ (k + 1)) by nia.
  assert (H2 : n * (a * (n + 1) ^ k) <= a * (n + 1) ^ (k + 1)).
  { rewrite Nat.pow_add_r, Nat.pow_1_r.
    replace (n * (a * (n + 1) ^ k)) with (a * ((n + 1) ^ k * n)) by ring.
    apply Nat.mul_le_mono_l. apply Nat.mul_le_mono_l. lia. }
  rewrite Nat.mul_add_distr_r. lia.
Qed.

Theorem additive_poly (T : nat -> nat) (c a k : nat) :
  T 0 <= c -> (forall n, T (n + 1) <= T n + a * (n + 1) ^ k) ->
  forall n, T n <= (c + a) * (n + 1) ^ (k + 1).
Proof.
  intros H0 Hstep n.
  apply Nat.le_trans with (c + n * (a * (n + 1) ^ k)).
  - apply (additive_bound T (fun n => a * (n + 1) ^ k) c H0 Hstep).
    intros m n' H. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. lia.
  - apply additive_poly_closed.
Qed.

(* (b) Multiplicative recurrences are exponential. *)

Theorem doubling_exact (T : nat -> nat) :
  T 0 = 1 -> (forall n, T (n + 1) = 2 * T n) -> forall n, T n = 2 ^ n.
Proof.
  intros H0 Hs n. induction n as [|n IH].
  - exact H0.
  - replace (S n) with (n + 1) by lia. rewrite Hs, IH.
    rewrite Nat.pow_add_r, Nat.pow_1_r. lia.
Qed.

Theorem branching_lower (T : nat -> nat) :
  1 <= T 0 -> (forall n, 2 * T n <= T (n + 1)) -> forall n, 2 ^ n <= T n.
Proof.
  intros H0 Hs n. induction n as [|n IH].
  - simpl. exact H0.
  - pose proof (Hs n) as H. replace (S n) with (n + 1) by lia.
    rewrite Nat.pow_add_r, Nat.pow_1_r. lia.
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
  2 ^ (2 * (c + k) + 1) <= n -> c * (n + 1) ^ k < 2 ^ n.
Proof.
  intros c d n Hn.
  assert (Hn1 : 1 <= n).
  { pose proof (Nat.pow_le_mono_r 2 0 (2 * (c + d) + 1) ltac:(lia) ltac:(lia)).
    rewrite Nat.pow_0_r in H. lia. }
  destruct (dyadic_bracket n Hn1) as [L [HL1 HL2]].
  assert (HLbig : 2 * (c + d) + 1 <= L).
  { destruct (Nat.le_gt_cases (2 * (c + d) + 1) L) as [H|H]; auto.
    pose proof (Nat.pow_le_mono_r 2 (L + 1) (2 * (c + d) + 1) ltac:(lia) ltac:(lia)).
    lia. }
  pose proof (linear_lt_exp (c + d) L HLbig) as Hlin.
  assert (Hsum : c + d * (L + 1) < n).
  { assert (c <= c * (L + 1)) by nia.
    rewrite Nat.mul_add_distr_r in Hlin. lia. }
  assert (Hbase : (n + 1) ^ d <= 2 ^ ((L + 1) * d)).
  { rewrite Nat.pow_mul_r. apply Nat.pow_le_mono_l. lia. }
  pose proof (lt_two_pow_self c) as Hc.
  assert (Hpos : 0 < 2 ^ ((L + 1) * d)).
  { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
  apply Nat.le_lt_trans with (c * 2 ^ ((L + 1) * d)).
  { apply Nat.mul_le_mono_l. exact Hbase. }
  apply Nat.lt_le_trans with (2 ^ c * 2 ^ ((L + 1) * d)).
  { apply Nat.mul_lt_mono_pos_r; auto. }
  rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
Qed.

(* Exponential beats every polynomial. *)
Theorem poly_lt_two_pow (c k : nat) : exists n, c * (n + 1) ^ k < 2 ^ n.
Proof. exists (2 ^ (2 * (c + k) + 1)). apply exp_beats_poly. lia. Qed.

(* Branching recurrences are not polynomial. *)
Theorem branching_not_poly (T : nat -> nat) :
  1 <= T 0 -> (forall n, 2 * T n <= T (n + 1)) ->
  ~ exists c k, forall n, T n <= c * (n + 1) ^ k.
Proof.
  intros H0 Hs [c [k Hb]].
  destruct (poly_lt_two_pow c k) as [n Hn].
  pose proof (branching_lower T H0 Hs n). pose proof (Hb n). lia.
Qed.

Theorem doubling_not_poly (T : nat -> nat) :
  T 0 = 1 -> (forall n, T (n + 1) = 2 * T n) ->
  forall c k, exists n, c * (n + 1) ^ k < T n.
Proof.
  intros H0 Hs c k. destruct (poly_lt_two_pow c k) as [n Hn].
  exists n. rewrite (doubling_exact T H0 Hs n). exact Hn.
Qed.

Fixpoint branchCost (q : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => 2 * branchCost q m + q m
  end.

(* Two-branch self-reduction is exponential, whatever the overhead. *)
Theorem branchCost_exponential (q : nat -> nat) : forall n, 2 ^ n <= branchCost q n.
Proof.
  apply branching_lower.
  - simpl. lia.
  - intro n. replace (n + 1) with (S n) by lia. simpl. lia.
Qed.

(* Self-reduction with one call: the obligation. *)

Fixpoint run {Inst : Type} (base : Inst -> bool) (step : Inst -> Inst) (n : nat) (I : Inst)
    : bool :=
  match n with
  | 0 => base I
  | S m => run base step m (step I)
  end.

Fixpoint runCost {Inst : Type} (baseCost stepCost : Inst -> nat) (step : Inst -> Inst)
    (n : nat) (I : Inst) : nat :=
  match n with
  | 0 => baseCost I
  | S m => stepCost I + runCost baseCost stepCost step m (step I)
  end.

(* Correctness by size induction. *)
Theorem run_correct {Inst : Type} (size : Inst -> nat) (answer base : Inst -> bool)
    (step : Inst -> Inst) :
  (forall I, size I = 0 -> base I = answer I) ->
  (forall I n, size I = n + 1 -> size (step I) = n /\ answer (step I) = answer I) ->
  forall n I, size I = n -> run base step n I = answer I.
Proof.
  intros Hbase Hstep n. induction n as [|n IH]; intros I HI.
  - apply Hbase. exact HI.
  - destruct (Hstep I n ltac:(lia)) as [H1 H2]. simpl.
    rewrite (IH (step I) H1). exact H2.
Qed.

(* Additive cost by size induction. *)
Theorem runCost_bound {Inst : Type} (size : Inst -> nat) (step : Inst -> Inst)
    (baseCost stepCost : Inst -> nat) (c a k : nat) :
  (forall I n, size I = n + 1 -> size (step I) = n) ->
  (forall I, baseCost I <= c) ->
  (forall I, stepCost I <= a * (size I + 1) ^ k) ->
  forall n I, size I = n -> runCost baseCost stepCost step n I <= c + n * (a * (n + 1) ^ k).
Proof.
  intros Hsize Hbc Hcost n. induction n as [|n IH]; intros I HI.
  - simpl. pose proof (Hbc I). lia.
  - pose proof (IH (step I) (Hsize I n ltac:(lia))) as H1.
    pose proof (Hcost I) as H2. rewrite HI in H2.
    assert (H3 : a * (n + 1) ^ k <= a * (S n + 1) ^ k).
    { apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. lia. }
    assert (H4 : n * (a * (n + 1) ^ k) <= n * (a * (S n + 1) ^ k))
      by (apply Nat.mul_le_mono_l; exact H3).
    assert (H5 : S n * (a * (S n + 1) ^ k) = n * (a * (S n + 1) ^ k) + a * (S n + 1) ^ k)
      by apply Nat.mul_succ_l.
    change (runCost baseCost stepCost step (S n) I)
      with (stepCost I + runCost baseCost stepCost step n (step I)).
    rewrite H5. lia.
Qed.

(* Open obligation: an additive-cost self-reduction. *)
Definition AdditiveSelfReduction {Inst : Type} (size : Inst -> nat) (answer : Inst -> bool)
    : Prop :=
  exists (base : Inst -> bool) (step : Inst -> Inst) (baseCost stepCost : Inst -> nat)
         (c a k : nat),
    (forall I, size I = 0 -> base I = answer I) /\ (forall I, baseCost I <= c) /\
    (forall I n, size I = n + 1 -> size (step I) = n /\ answer (step I) = answer I) /\
    (forall I, stepCost I <= a * (size I + 1) ^ k).

(* The obligation yields a correct solver with polynomial cost. *)
Theorem obligation_gives_poly_solver {Inst : Type} (size : Inst -> nat)
    (answer : Inst -> bool) :
  AdditiveSelfReduction size answer ->
  exists (solve : Inst -> bool) (cost : Inst -> nat) (c' k' : nat),
    forall I, solve I = answer I /\ cost I <= c' * (size I + 1) ^ k'.
Proof.
  intros [base [step [baseCost [stepCost [c [a [k [Hbase [Hbc [Hstep Hcost]]]]]]]]]].
  exists (fun I => run base step (size I) I),
         (fun I => runCost baseCost stepCost step (size I) I), (c + a), (k + 1).
  intro I. split.
  - apply (run_correct size answer base step Hbase Hstep (size I) I). reflexivity.
  - apply Nat.le_trans with (c + size I * (a * (size I + 1) ^ k)).
    + apply (runCost_bound size step baseCost stepCost c a k); auto.
      intros I' n H. apply (Hstep I' n H).
    + apply additive_poly_closed.
Qed.

(* Explicit solver bound: for any data meeting the conditions of AdditiveSelfReduction,
   the specific solver run base step (size I) is correct and its cost runCost is at most
   (c + a) * (size I + 1) ^ (k + 1). *)
Theorem self_reduction_solver_bound {Inst : Type} (size : Inst -> nat)
    (answer base : Inst -> bool) (step : Inst -> Inst) (baseCost stepCost : Inst -> nat)
    (c a k : nat) :
  (forall I, size I = 0 -> base I = answer I) -> (forall I, baseCost I <= c) ->
  (forall I n, size I = n + 1 -> size (step I) = n /\ answer (step I) = answer I) ->
  (forall I, stepCost I <= a * (size I + 1) ^ k) ->
  forall I, run base step (size I) I = answer I /\
    runCost baseCost stepCost step (size I) I <= (c + a) * (size I + 1) ^ (k + 1).
Proof.
  intros Hbase Hbc Hstep Hcost I. split.
  - apply (run_correct size answer base step Hbase Hstep (size I) I). reflexivity.
  - apply Nat.le_trans with (c + size I * (a * (size I + 1) ^ k)).
    + apply (runCost_bound size step baseCost stepCost c a k); auto.
      intros I' n H. apply (Hstep I' n H).
    + apply additive_poly_closed.
Qed.

Example branchCost_check : branchCost (fun _ => 0) 5 = 32.
Proof. reflexivity. Qed.
