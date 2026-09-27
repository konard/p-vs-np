(* Issue #532, Idea 17: enumeration accounting (exponential versus polynomial).

   Rocq counterpart of lean/Idea17.lean.  Proves, for every n, that the
   enumeration of length-n Boolean vectors has length 2^n, is duplicate-free
   and complete; that brute force is correct and costs 2^n on a predicate with
   no witness; and that c * (n+1)^k < 2^n for all n >= 2^(2(c+k)+1).
   Verdict: exhaustive enumeration is refuted as polynomial in general, but
   the enumeration count is not a lower bound for the problem
   (enumeration_cost_is_not_problem_cost); the real obligation
   AllAlgorithmsSuperpolynomial is only defined, not proved. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* ---------- Enumeration of Boolean vectors ---------- *)

Fixpoint allVecs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allVecs n') ++ map (cons true) (allVecs n')
  end.

Theorem allVecs_length : forall n, length (allVecs n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allVecs : forall n v, In v (allVecs n) <-> length v = n.
Proof.
  induction n as [|n IH]; intros v; simpl.
  - split.
    + intros [H|[]]. subst. reflexivity.
    + intros H. destruct v; [left; reflexivity | discriminate].
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; subst; simpl; f_equal; apply IH; exact Hin.
    + intros H. destruct v as [|b w]; [discriminate|].
      simpl in H. injection H as H.
      destruct b; [right|left]; exists w; split; auto; apply IH; exact H.
Qed.

Lemma nodup_map_cons : forall (b : bool) (l : list (list bool)),
  NoDup l -> NoDup (map (cons b) l).
Proof.
  intros b l H. induction H as [|x l Hx Hl IH]; simpl; constructor; auto.
  intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  injection Hy as Hy. subst. contradiction.
Qed.

Lemma nodup_app : forall (A : Type) (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1. induction H1 as [|x l1 Hx Hl1 IH]; intros H2 Hdis; simpl; auto.
  constructor.
  - rewrite in_app_iff. intros [H|H]; [contradiction|].
    apply (Hdis x); simpl; auto.
  - apply IH; auto. intros a Ha. apply Hdis. simpl; auto.
Qed.

Theorem allVecs_nodup : forall n, NoDup (allVecs n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; auto | constructor].
  - apply nodup_app; try apply nodup_map_cons; auto.
    intros a Ha Hb. apply in_map_iff in Ha. apply in_map_iff in Hb.
    destruct Ha as [x [Hx _]]. destruct Hb as [y [Hy _]]. subst.
    discriminate.
Qed.

(* ---------- Brute-force search and its exact cost ---------- *)

Definition bruteForce (f : list bool -> bool) (n : nat) : bool :=
  existsb f (allVecs n).

Theorem bruteForce_correct : forall f n,
  bruteForce f n = true <-> exists v, length v = n /\ f v = true.
Proof.
  intros f n. unfold bruteForce. rewrite existsb_exists. split.
  - intros [v [Hv Hf]]. exists v. split; auto. apply mem_allVecs; auto.
  - intros [v [Hv Hf]]. exists v. split; auto. apply mem_allVecs; auto.
Qed.

Fixpoint searchCost (f : list bool -> bool) (l : list (list bool)) : nat :=
  match l with
  | [] => 0
  | v :: vs => if f v then 1 else 1 + searchCost f vs
  end.

Theorem searchCost_all_false : forall f l,
  (forall v, In v l -> f v = false) -> searchCost f l = length l.
Proof.
  intros f l. induction l as [|v vs IH]; intros H; simpl; auto.
  rewrite (H v (or_introl eq_refl)). rewrite IH; auto.
  intros w Hw. apply H. simpl; auto.
Qed.

Theorem searchCost_no_witness : forall f n,
  (forall v, length v = n -> f v = false) -> searchCost f (allVecs n) = 2 ^ n.
Proof.
  intros f n H. rewrite searchCost_all_false.
  - apply allVecs_length.
  - intros v Hv. apply H. apply mem_allVecs; auto.
Qed.

(* ---------- Exponential beats every polynomial ---------- *)

(* Local mirror of Complexity.Polynomial.eval: coefficient c, degree k. *)
Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

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

(* Growth theorem: for all n >= 2^(2(c+k)+1), c * (n+1)^k < 2^n. *)
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

Theorem exists_threshold : forall c k,
  exists N, forall n, N <= n -> c * (n + 1) ^ k < 2 ^ n.
Proof.
  intros c k. exists (2 ^ (2 * (c + k) + 1)). intros n Hn.
  apply (exp_beats_poly c k n Hn).
Qed.

Theorem enumeration_not_polynomial : forall c k,
  exists N, forall n, N <= n ->
    polyEval c k n < length (allVecs n) /\
    polyEval c k n < searchCost (fun _ => false) (allVecs n).
Proof.
  intros c k. exists (2 ^ (2 * (c + k) + 1)). intros n Hn.
  rewrite allVecs_length, searchCost_no_witness by reflexivity.
  pose proof (exp_beats_poly c k n Hn). split; auto.
Qed.

(* ---------- What the accounting does not show ---------- *)

Theorem enumeration_cost_is_not_problem_cost : forall n,
  searchCost (fun _ => false) (allVecs n) = 2 ^ n /\
  bruteForce (fun _ => false) n = (fun _ => false) n.
Proof.
  intros n. split.
  - apply searchCost_no_witness. reflexivity.
  - destruct (bruteForce (fun _ => false) n) eqn:E; auto.
    apply bruteForce_correct in E. destruct E as [v [_ Hv]]. discriminate.
Qed.

Record AlgorithmModel := {
  Alg : Type;
  correct : Alg -> Prop;
  cost : Alg -> nat -> nat
}.

Definition PolyBounded (M : AlgorithmModel) (A : Alg M) : Prop :=
  exists c k, forall n, cost M A n <= polyEval c k n.

(* Open obligation: every correct algorithm is super-polynomial.  Instantiated
   with polynomial-time machines deciding SAT this is P <> NP.  Only defined. *)
Definition AllAlgorithmsSuperpolynomial (M : AlgorithmModel) : Prop :=
  forall A, correct M A -> forall c k N, exists n, N <= n /\ polyEval c k n < cost M A n.

Theorem superpolynomial_excludes_poly : forall M,
  AllAlgorithmsSuperpolynomial M -> forall A, correct M A -> ~ PolyBounded M A.
Proof.
  intros M H A HA [c [k Hb]].
  destruct (H A HA c k 0) as [n [_ Hn]].
  specialize (Hb n). lia.
Qed.

Definition twoAlgModel : AlgorithmModel := {|
  Alg := bool;
  correct := fun _ => True;
  cost := fun a n => if a then 1 else 2 ^ n
|}.

Theorem one_slow_algorithm_is_not_a_lower_bound :
  (forall c k N, exists n, N <= n /\ polyEval c k n < cost twoAlgModel false n) /\
  ~ AllAlgorithmsSuperpolynomial twoAlgModel.
Proof.
  split.
  - intros c k N. exists (N + 2 ^ (2 * (c + k) + 1)). split; [lia|].
    change (polyEval c k (N + 2 ^ (2 * (c + k) + 1)) < 2 ^ (N + 2 ^ (2 * (c + k) + 1))).
    apply exp_beats_poly. lia.
  - intros H. destruct (H true I 1 0 0) as [n [_ Hn]].
    simpl in Hn. unfold polyEval in Hn. simpl in Hn. lia.
Qed.
