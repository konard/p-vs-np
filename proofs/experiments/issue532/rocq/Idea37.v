(* Issue #532, Idea 37: parameterized structure.

   Rocq counterpart of ../lean/Idea37.lean (same theorem names and content).
   An FPT bound f(k) * n^c is polynomial when f(k) <= n^a, in particular when
   2^k <= n (logarithmic parameter). When the parameter equals the input size,
   2^n * n^c exceeds every polynomial a * (n+1)^d somewhere. An FPT algorithm
   with a parameter that is logarithmic on all instances is a polynomial-time
   algorithm; for an NP-complete problem that is the open obligation.
   All proofs are constructive. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.

Theorem tested (cost : nat -> nat) (k cap : nat) :
  (forall a b, a <= b -> cost a <= cost b) ->
  k <= cap -> cost k <= cost cap.
Proof. intros Hmono Hbound; apply Hmono, Hbound. Qed.

(* (a) Bounded parameter functions give polynomial time. *)

Theorem fpt_param_bound_poly (f : nat -> nat) (k n a c : nat) :
  f k <= n ^ a -> f k * n ^ c <= n ^ (a + c).
Proof. intro H. rewrite Nat.pow_add_r. apply Nat.mul_le_mono_r. exact H. Qed.

Theorem fpt_log_param_poly (k n c : nat) :
  2 ^ k <= n -> 2 ^ k * n ^ c <= n ^ (c + 1).
Proof.
  intro H. replace (c + 1) with (S c) by lia. rewrite Nat.pow_succ_r'.
  apply Nat.mul_le_mono_r. exact H.
Qed.

(* (b) Exponential beats every polynomial. *)

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

Theorem exp_beats_poly : forall c d n,
  2 ^ (2 * (c + d) + 1) <= n -> c * (n + 1) ^ d < 2 ^ n.
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

Theorem exists_threshold : forall c d,
  exists N, forall n, N <= n -> c * (n + 1) ^ d < 2 ^ n.
Proof.
  intros c d. exists (2 ^ (2 * (c + d) + 1)). intros n Hn.
  apply (exp_beats_poly c d n Hn).
Qed.

Theorem poly_lt_two_pow (c d : nat) : exists n, c * (n + 1) ^ d < 2 ^ n.
Proof.
  destruct (exists_threshold c d) as [N HN]. exists N. apply HN. lia.
Qed.

Theorem fpt_full_param_not_poly (a d c : nat) :
  exists n, a * (n + 1) ^ d < 2 ^ n * n ^ c.
Proof.
  destruct (exists_threshold a d) as [N HN]. exists (N + 1).
  pose proof (HN (N + 1) ltac:(lia)) as H1.
  assert (Hpos : 1 <= (N + 1) ^ c).
  { pose proof (Nat.pow_le_mono_l 1 (N + 1) c ltac:(lia)) as Hp.
    rewrite Nat.pow_1_l in Hp. exact Hp. }
  apply Nat.lt_le_trans with (2 ^ (N + 1)); [exact H1|].
  rewrite <- (Nat.mul_1_r (2 ^ (N + 1))) at 1.
  apply Nat.mul_le_mono_l. exact Hpos.
Qed.

(* The obligation. *)

Definition FPTBound {Inst : Type} (time size param : Inst -> nat) (f : nat -> nat) (c : nat) : Prop :=
  forall I, time I <= f (param I) * size I ^ c.

Definition LogBoundedParam {Inst : Type} (size param : Inst -> nat) (b : nat) : Prop :=
  forall I, 2 ^ param I <= size I ^ b.

Theorem fpt_log_param_polytime {Inst : Type} (time size param : Inst -> nat) (c b : nat) :
  FPTBound time size param (fun k => 2 ^ k) c ->
  LogBoundedParam size param b ->
  forall I, time I <= size I ^ (b + c).
Proof.
  intros Hfpt Hlog I.
  apply Nat.le_trans with (2 ^ param I * size I ^ c); [apply Hfpt|].
  apply (fpt_param_bound_poly (fun k => 2 ^ k)). apply Hlog.
Qed.

Definition LogParamFPTObligation {Inst Alg : Type} (Correct : Alg -> Prop)
    (time : Alg -> Inst -> nat) (size : Inst -> nat) : Prop :=
  exists (A : Alg) (param : Inst -> nat) (c b : nat),
    Correct A /\ FPTBound (time A) size param (fun k => 2 ^ k) c /\ LogBoundedParam size param b.

Theorem obligation_gives_poly_time {Inst Alg : Type} (Correct : Alg -> Prop)
    (time : Alg -> Inst -> nat) (size : Inst -> nat) :
  LogParamFPTObligation Correct time size ->
  exists A d, Correct A /\ forall I, time A I <= size I ^ d.
Proof.
  intros [A [param [c [b [HA [Hfpt Hlog]]]]]].
  exists A, (b + c). split; [exact HA|].
  apply (fpt_log_param_polytime (time A) size param c b Hfpt Hlog).
Qed.

Example numeric_check : 2 ^ 4 * 16 ^ 2 <= 16 ^ 3.
Proof. apply Nat.leb_le. reflexivity. Qed.
