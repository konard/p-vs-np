(* Issue #532, Idea 17: enumeration accounting (exponential versus polynomial).

   Rocq counterpart of ../lean/Idea17.lean.  Proves, for every n, that the
   enumeration allVecs n of length-n Boolean vectors has length 2^n, is
   duplicate-free and complete; that brute force is correct and costs 2^n on
   a predicate with no witness; and that c * (n+1)^k < 2^n for all
   n >= 2^(2(c+k)+1) (polyEval_eq identifies the left side with
   Complexity.evalPoly).  Verdict: exhaustive enumeration is refuted as
   polynomial in general, but the enumeration count is not a lower bound for
   the problem (enumeration_cost_is_not_problem_cost).

   The schema AllAlgorithmsSuperpolynomialFor M is instantiated on the shared
   machine model (Machines.v) by machineModel L: the algorithms are machines
   that halt with the answer L x on every input (TotalDecider), and the cost at
   length n is the worst Run step count over the 2^n inputs of length n
   (worstTime).  The open obligation is SATMachinesSuperpolynomial; it rules
   out InP SAT (not_inP_sat_of_satMachinesSuperpolynomial), gives PNotEqualsNP
   with SATInNP (pNotEqualsNP_of_satMachinesSuperpolynomial) and is equivalent
   to PNotEqualsNP with CookLevin and excluded middle
   (satMachinesSuperpolynomial_iff_pNotEqualsNP).  Non-vacuity: the schema
   fails for the constant-false language, whose one-step machine has
   worst-case cost 1 (worstTime_emptyMachine), and holds for Machines.Diag
   (diag_superpolynomial).

   Differences from Lean:
   - runTime is computable.  haltsAt m c t decides whether m halts after
     exactly t steps (haltsAt_iff), and runTime m h x finds that t by the
     axiom-free linear search of Stdlib.ConstructiveEpsilon.  The search needs
     a proof h : Halts m that m halts on every input, so runTime and worstTime
     take h as an extra argument (Lean returns 0 on non-halting inputs by
     classical choice).  runTime_eq shows the value does not depend on h.
   - machineModel L has as algorithms the pairs {m | TotalDecider m L} (the
     cost needs the halting proof), with correct := fun _ => True.
     SATMachinesSuperpolynomial quantifies over m and h : TotalDecider m SAT
     exactly as in Lean, with worstTime m (totalDecider_halts m SAT h).
   - allMachinesSuperpolynomial_iff_not_inP, satMachinesSuperpolynomial_iff_not_inP
     and satMachinesSuperpolynomial_iff_pNotEqualsNP take excluded middle as an
     explicit premise classic : forall P : Prop, P \/ ~ P (Lean uses
     Classical.byContradiction in the same direction).  The other direction
     is proved without it (allMachinesSuperpolynomial_not_inP,
     not_inP_sat_of_satMachinesSuperpolynomial).
   - diag_superpolynomial is proved directly by a pointwise diagonal (the code
     of the pair (m, c + N, k) is an input of length >= N on which m cannot
     halt within the polynomial), not through the classical equivalence.
   No axioms are used.  Nothing here proves the obligation. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia ConstructiveEpsilon.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(* Local mirror of Complexity.evalPoly: coefficient c, degree k. *)
Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

(* polyEval is the repository's polynomial evaluation. *)
Theorem polyEval_eq : forall c k n,
  polyEval c k n = evalPoly {| coefficient := c; degree := k |} n.
Proof. reflexivity. Qed.

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

(** Schema (the shape of a lower-bound statement over an arbitrary model).
    Every correct algorithm in the model has super-polynomial cost: for each
    polynomial there are arbitrarily large lengths where the cost exceeds it.
    The model [M] is free, so this is a schema, not a claim; its instance on
    the shared machine model is [SATMachinesSuperpolynomial] below. *)
Definition AllAlgorithmsSuperpolynomialFor (M : AlgorithmModel) : Prop :=
  forall A, correct M A -> forall c k N, exists n, N <= n /\ polyEval c k n < cost M A n.

Theorem superpolynomial_excludes_poly : forall M,
  AllAlgorithmsSuperpolynomialFor M -> forall A, correct M A -> ~ PolyBounded M A.
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
  ~ AllAlgorithmsSuperpolynomialFor twoAlgModel.
Proof.
  split.
  - intros c k N. exists (N + 2 ^ (2 * (c + k) + 1)). split; [lia|].
    change (polyEval c k (N + 2 ^ (2 * (c + k) + 1)) < 2 ^ (N + 2 ^ (2 * (c + k) + 1))).
    apply exp_beats_poly. lia.
  - intros H. destruct (H true I 1 0 0) as [n [_ Hn]].
    simpl in Hn. unfold polyEval in Hn. simpl in Hn. lia.
Qed.

(* ---------- The schema on the shared machine model ---------- *)

(** [m] halts with the answer [L x] on every input (no time bound). *)
Definition TotalDecider (m : Machine) (L : Language) : Prop :=
  forall x, exists t, Run m (initial x) t (L x).

(** [haltsAt m c t] holds when [m] started in [c] halts after exactly [t]
    steps. *)
Fixpoint haltsAt (m : Machine) (c : Config) (t : nat) : bool :=
  match t with
  | 0 => false
  | S t' => match step m c with
            | inl _ => Nat.eqb t' 0
            | inr c' => haltsAt m c' t'
            end
  end.

Theorem haltsAt_iff : forall m t c, haltsAt m c t = true <-> exists b, Run m c t b.
Proof.
  intros m t. induction t as [| t IH]; intros c; simpl.
  - split; [discriminate |]. intros [b hr]. inversion hr.
  - destruct (step m c) as [b | c'] eqn:hs.
    + split.
      * intro h. apply Nat.eqb_eq in h. subst t. exists b. apply run_halt. exact hs.
      * intros [b' hr]. inversion hr as [c0 b0 hs' | c0 c1 t0 b0 hs' hr']; subst.
        -- reflexivity.
        -- rewrite hs in hs'. discriminate.
    + split.
      * intro h. destruct (proj1 (IH c') h) as [b hr]. exists b.
        apply run_next with c'; assumption.
      * intros [b hr]. inversion hr as [c0 b0 hs' | c0 c1 t0 b0 hs' hr']; subst.
        -- rewrite hs in hs'. discriminate.
        -- rewrite hs in hs'. injection hs' as <-. apply IH. exists b. exact hr'.
Qed.

(** [m] halts on every input. *)
Definition Halts (m : Machine) : Prop :=
  forall x, exists t, haltsAt m (initial x) t = true.

Theorem totalDecider_halts : forall m L, TotalDecider m L -> Halts m.
Proof.
  intros m L h x. destruct (h x) as [t hr]. exists t. apply haltsAt_iff.
  exists (L x). exact hr.
Qed.

(** The [Run] step count of [m] on [x], found by an axiom-free linear
    search (runs are unique by [run_deterministic]). *)
Definition runTime (m : Machine) (h : Halts m) (x : Word) : nat :=
  proj1_sig (constructive_indefinite_ground_description_nat
    (fun t => haltsAt m (initial x) t = true)
    (fun t => bool_dec (haltsAt m (initial x) t) true) (h x)).

Theorem runTime_eq : forall m (h : Halts m) x t b,
  Run m (initial x) t b -> runTime m h x = t.
Proof.
  intros m h x t b hr. unfold runTime.
  destruct (constructive_indefinite_ground_description_nat _ _ _) as [t' ht']. simpl.
  destruct (proj1 (haltsAt_iff _ _ _) ht') as [b' hr'].
  exact (proj1 (run_deterministic _ _ _ _ _ _ hr' hr)).
Qed.

(** Worst-case step count of [m] over the [2 ^ n] inputs of length [n],
    computed over the enumeration [allVecs n]. *)
Definition worstTime (m : Machine) (h : Halts m) (n : nat) : nat :=
  fold_right max 0 (map (runTime m h) (allVecs n)).

Lemma le_foldr_max : forall (l : list nat) a, In a l -> a <= fold_right max 0 l.
Proof.
  intros l a. induction l as [| y l IH]; simpl; [contradiction |].
  intros [<- | hin]; [lia |]. specialize (IH hin). lia.
Qed.

Lemma foldr_max_le : forall (l : list nat) B, (forall a, In a l -> a <= B) ->
  fold_right max 0 l <= B.
Proof.
  intros l B. induction l as [| y l IH]; simpl; intro h; [lia |].
  apply Nat.max_lub; [apply h; left; reflexivity |].
  apply IH. intros a ha. apply h. right. exact ha.
Qed.

Theorem runTime_le_worstTime : forall m (h : Halts m) x,
  runTime m h x <= worstTime m h (length x).
Proof.
  intros m h x. apply le_foldr_max. apply in_map. apply mem_allVecs. reflexivity.
Qed.

Theorem worstTime_le : forall m (h : Halts m) n B,
  (forall x : Word, length x = n -> runTime m h x <= B) -> worstTime m h n <= B.
Proof.
  intros m h n B hB. apply foldr_max_le. intros a ha.
  apply in_map_iff in ha. destruct ha as [x [<- hx]].
  apply hB. apply mem_allVecs. exact hx.
Qed.

(** The shared machine model as an [AlgorithmModel] for [L]: algorithms are
    machines that decide [L] on every input (with that proof attached), and
    the cost at length [n] is the worst-case [Run] step count. *)
Definition machineModel (L : Language) : AlgorithmModel := {|
  Alg := { m : Machine | TotalDecider m L };
  correct := fun _ => True;
  cost := fun A n => worstTime (proj1_sig A) (totalDecider_halts _ L (proj2_sig A)) n
|}.

(** The schema on the machine model excludes [InP L] (no excluded middle
    needed in this direction). *)
Theorem allMachinesSuperpolynomial_not_inP : forall L,
  AllAlgorithmsSuperpolynomialFor (machineModel L) -> ~ InP L.
Proof.
  intros L h hP.
  destruct (proj2 (polyDec_iff_inP L) hP) as [m [p hd]].
  assert (hm : TotalDecider m L).
  { intro x. destruct (hd x) as [t [b [_ [hr hb]]]]. exists t. rewrite <- hb. exact hr. }
  destruct (h (exist _ m hm) I (coefficient p) (degree p) 0) as [n [_ hn]].
  simpl in hn.
  assert (hle : worstTime m (totalDecider_halts m L hm) n <= evalPoly p n).
  { apply worstTime_le. intros x hx. destruct (hd x) as [t [b [ht [hr _]]]].
    rewrite (runTime_eq _ _ _ _ _ hr). subst n. exact ht. }
  unfold polyEval, evalPoly in *. lia.
Qed.

(** On the machine model the schema is exactly "not in P" (the backward
    direction uses excluded middle, passed as the premise [classic]). *)
Theorem allMachinesSuperpolynomial_iff_not_inP :
  (forall P : Prop, P \/ ~ P) -> forall L,
  AllAlgorithmsSuperpolynomialFor (machineModel L) <-> ~ InP L.
Proof.
  intros classic L. split; [apply allMachinesSuperpolynomial_not_inP |].
  intros hnot [m hm] _ c k N. simpl.
  set (W := worstTime m (totalDecider_halts m L hm)).
  destruct (classic (exists n, N <= n /\ polyEval c k n < W n)) as [H | Hno]; [exact H |].
  exfalso.
  assert (hbig : forall n, N <= n -> W n <= polyEval c k n).
  { intros n hn. destruct (Nat.le_gt_cases (W n) (polyEval c k n)) as [hle | hgt];
      [exact hle |]. exfalso. apply Hno. exists n. split; assumption. }
  set (B := fold_right max 0 (map W (seq 0 N))).
  assert (hall : forall n, W n <= polyEval (B + c) k n).
  { intro n. unfold polyEval.
    assert (hpos : 0 < (n + 1) ^ k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    destruct (Nat.le_gt_cases N n) as [hn | hn].
    - pose proof (hbig n hn) as h1. unfold polyEval in h1. nia.
    - assert (h1 : W n <= B).
      { apply le_foldr_max. apply in_map. apply in_seq. lia. }
      nia. }
  apply hnot. apply (inP_of_decidesWithin m {| coefficient := B + c; degree := k |}).
  intro x. destruct (hm x) as [t hr]. exists t, (L x).
  split; [| split; [exact hr | reflexivity]].
  pose proof (runTime_le_worstTime m (totalDecider_halts m L hm) x) as h1.
  rewrite (runTime_eq _ _ _ _ _ hr) in h1.
  pose proof (hall (length x)) as h2. fold W in h1. unfold polyEval in h2.
  unfold evalPoly. simpl. lia.
Qed.

(** Open obligation (the lower bound for SAT on the shared machine model).
    Every [Machine] that halts with the answer [SAT x] on every input has,
    for each polynomial [c * (n + 1) ^ k], arbitrarily large lengths [n] at
    which its worst-case [Run] step count over inputs of length [n] exceeds
    the polynomial.  Equivalent to [~ InP SAT]
    ([satMachinesSuperpolynomial_iff_not_inP]). *)
Definition SATMachinesSuperpolynomial : Prop :=
  forall (m : Machine) (h : TotalDecider m SAT) (c k N : nat),
    exists n, N <= n /\ polyEval c k n < worstTime m (totalDecider_halts m SAT h) n.

(* The obligation is the schema instantiated on the machine model for SAT. *)
Theorem satMachinesSuperpolynomial_iff_for :
  SATMachinesSuperpolynomial <-> AllAlgorithmsSuperpolynomialFor (machineModel SAT).
Proof.
  split.
  - intros h [m hm] _ c k N. exact (h m hm c k N).
  - intros h m hm c k N. exact (h (exist _ m hm) I c k N).
Qed.

Theorem not_inP_sat_of_satMachinesSuperpolynomial :
  SATMachinesSuperpolynomial -> ~ InP SAT.
Proof.
  intro h. apply allMachinesSuperpolynomial_not_inP.
  apply satMachinesSuperpolynomial_iff_for. exact h.
Qed.

Theorem satMachinesSuperpolynomial_iff_not_inP :
  (forall P : Prop, P \/ ~ P) -> (SATMachinesSuperpolynomial <-> ~ InP SAT).
Proof.
  intro classic. rewrite satMachinesSuperpolynomial_iff_for.
  apply allMachinesSuperpolynomial_iff_not_inP. exact classic.
Qed.

(* Conditional theorem.  With SATInNP, the obligation gives P <> NP. *)
Theorem pNotEqualsNP_of_satMachinesSuperpolynomial :
  SATInNP -> SATMachinesSuperpolynomial -> PNotEqualsNP.
Proof.
  intros mem h hPNP. apply (not_inP_sat_of_satMachinesSuperpolynomial h).
  exact (inP_sat_of_pEqualsNP mem hPNP).
Qed.

(* With the Cook-Levin premise the obligation is equivalent to P <> NP. *)
Theorem satMachinesSuperpolynomial_iff_pNotEqualsNP :
  (forall P : Prop, P \/ ~ P) -> CookLevin -> (SATMachinesSuperpolynomial <-> PNotEqualsNP).
Proof.
  intros classic hCL. rewrite (satMachinesSuperpolynomial_iff_not_inP classic).
  pose proof (inP_sat_iff hCL) as E. unfold PNotEqualsNP.
  split; intros H H'; apply H; apply E; exact H'.
Qed.

(* ---------- Non-vacuity on the machine model ---------- *)

Definition emptyMachine : Machine := {| program := [] |}.

(* The machine with no instructions halts with false after one step. *)
Theorem emptyMachine_run : forall x, Run emptyMachine (initial x) 1 false.
Proof. intro x. apply run_halt. destruct x; reflexivity. Qed.

Theorem emptyMachine_totalDecider : TotalDecider emptyMachine (fun _ => false).
Proof. intro x. exists 1. apply emptyMachine_run. Qed.

(* Machine form of enumeration_cost_is_not_problem_cost: the constant-false
   language, whose brute-force search costs 2 ^ n, has a machine decider with
   worst-case cost 1 at every length. *)
Theorem worstTime_emptyMachine : forall (h : Halts emptyMachine) n,
  worstTime emptyMachine h n = 1.
Proof.
  intros h n. apply Nat.le_antisymm.
  - apply worstTime_le. intros x _. rewrite (runTime_eq _ _ _ _ _ (emptyMachine_run x)).
    lia.
  - pose proof (runTime_le_worstTime emptyMachine h (repeat false n)) as H.
    rewrite (runTime_eq _ _ _ _ _ (emptyMachine_run _)), repeat_length in H. exact H.
Qed.

Theorem inP_const_false : InP (fun _ => false).
Proof.
  apply (inP_of_decidesWithin emptyMachine {| coefficient := 1; degree := 0 |}).
  intro x. exists 1, false. split; [unfold evalPoly; simpl; lia |].
  split; [apply emptyMachine_run | reflexivity].
Qed.

(* Non-vacuity, false side: the machine-model statement fails for the
   constant-false language. *)
Theorem const_false_not_superpolynomial :
  ~ AllAlgorithmsSuperpolynomialFor (machineModel (fun _ => false)).
Proof. intro h. exact (allMachinesSuperpolynomial_not_inP _ h inP_const_false). Qed.

Lemma length_encNat : forall n, length (encNat n) = S n.
Proof. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* Non-vacuity, true side: the machine-model statement holds for the diagonal
   language Diag.  Pointwise diagonal: on the code w of (m, c + N, k), a
   machine deciding Diag cannot halt within (c + N) * (|w| + 1) ^ k steps, and
   |w| >= N. *)
Theorem diag_superpolynomial : AllAlgorithmsSuperpolynomialFor (machineModel Diag).
Proof.
  intros [m hm] _ c k N. simpl.
  set (p := {| coefficient := c + N; degree := k |}).
  set (w := encMachinePoly (m, p)).
  exists (length w). split.
  - unfold w, encMachinePoly. rewrite !length_app. simpl. rewrite length_encNat. lia.
  - destruct (hm w) as [t hr].
    pose proof (runTime_le_worstTime m (totalDecider_halts m Diag hm) w) as h1.
    rewrite (runTime_eq _ _ _ _ _ hr) in h1.
    assert (hgt : evalPoly p (length w) < t).
    { destruct (Nat.le_gt_cases t (evalPoly p (length w))) as [hle | hgt]; [| exact hgt].
      exfalso. pose proof (runFor_of_run _ _ _ _ hr _ hle) as hrun.
      assert (hD : Diag w = negb (clockedLanguage (m, p) w)).
      { unfold Diag. unfold w at 1. rewrite decMachinePoly_encMachinePoly. reflexivity. }
      unfold clockedLanguage in hD. simpl fst in hD. simpl snd in hD.
      rewrite hrun in hD. destruct (Diag w); discriminate. }
    assert (hp : polyEval c k (length w) <= evalPoly p (length w)).
    { unfold polyEval, evalPoly, p. simpl. apply Nat.mul_le_mono_r. lia. }
    lia.
Qed.

(* The shape of SATMachinesSuperpolynomial is satisfiable and refutable. *)
Theorem machine_schema_nontrivial :
  (exists L, AllAlgorithmsSuperpolynomialFor (machineModel L)) /\
  (exists L, ~ AllAlgorithmsSuperpolynomialFor (machineModel L)).
Proof.
  split; [exists Diag; exact diag_superpolynomial |].
  exists (fun _ => false). exact const_false_not_superpolynomial.
Qed.
