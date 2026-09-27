(* Issue #532, Idea 09: description length versus running time.

   Rocq counterpart of lean/Idea09.lean; theorem names are aligned.

   Part A: a loop language (Inc, Seq, Loop k b) with honest description
   length (a loop counter k costs bits k = 1 + log2 k symbols) and step
   costs.  We prove for every program that it adds [gain p] in exactly
   [cost p] steps, that [gain p <= cost p], that time-optimal programs are
   loop-free and then have size = cost, and that for every k >= 6 every
   program for v |-> v + k no longer than [Loop k Inc] is strictly slower
   than the fastest program (shortest_is_never_fastest).

   Part B: abstract Levin universal search with restart semantics:
   soundness, completeness by phase i + L when t <= 2^L, total work
   < 2^(J+2), the bound totalWork < 8 * 2^i * t, and the conditional
   theorem from the open obligation PolyTimeWitnessProgramExists.

   Verdict: "shortest implies fastest" refuted as a route; Levin search
   developed; whether it is polynomial is the open obligation (equivalent to
   P = NP for SAT).  Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool.

(** * Part A *)

(** Binary length: [bits n = 1 + log2 n] (so [bits 0 = bits 1 = 1]); this
    agrees with the recursive definition used in the Lean file. *)
Definition bits (n : nat) : nat := S (Nat.log2 n).

Theorem bits_spec : forall n, 1 <= n -> n < 2 ^ bits n /\ 2 ^ bits n <= 2 * n.
Proof.
  intros n Hn. destruct (Nat.log2_spec n) as [H1 H2]; [lia |].
  unfold bits. rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r' in H2. lia.
Qed.

Inductive Prog : Type :=
| Inc : Prog
| Seq : Prog -> Prog -> Prog
| Loop : nat -> Prog -> Prog.

Fixpoint size (p : Prog) : nat :=
  match p with
  | Inc => 1
  | Seq p q => size p + size q
  | Loop k b => bits k + 1 + size b
  end.

Fixpoint iter (k : nat) (f : nat -> nat * nat) (v : nat) : nat * nat :=
  match k with
  | 0 => (v, 1)
  | S k' =>
      let r := f v in
      let r2 := iter k' f (fst r) in
      (fst r2, snd r + 1 + snd r2)
  end.

Fixpoint run (p : Prog) (v : nat) : nat * nat :=
  match p with
  | Inc => (v + 1, 1)
  | Seq p q =>
      let r := run p v in
      let r2 := run q (fst r) in
      (fst r2, snd r + snd r2)
  | Loop k b => iter k (run b) v
  end.

Fixpoint gain (p : Prog) : nat :=
  match p with
  | Inc => 1
  | Seq p q => gain p + gain q
  | Loop k b => k * gain b
  end.

Fixpoint cost (p : Prog) : nat :=
  match p with
  | Inc => 1
  | Seq p q => cost p + cost q
  | Loop k b => k * (cost b + 1) + 1
  end.

Fixpoint loopFree (p : Prog) : bool :=
  match p with
  | Inc => true
  | Seq p q => loopFree p && loopFree q
  | Loop _ _ => false
  end.

Theorem iter_eq : forall (f : nat -> nat * nat) (g c : nat),
  (forall v, f v = (v + g, c)) ->
  forall k v, iter k f v = (v + k * g, k * (c + 1) + 1).
Proof.
  intros f g c Hf k. induction k as [| k IH]; intros v; simpl.
  - f_equal; lia.
  - rewrite Hf. simpl. rewrite IH. simpl. f_equal; lia.
Qed.

(** Every program maps [v] to [v + gain p] using exactly [cost p] steps. *)
Theorem run_eq : forall p v, run p v = (v + gain p, cost p).
Proof.
  induction p as [| p IHp q IHq | k b IHb]; intros v; simpl.
  - reflexivity.
  - rewrite IHp. simpl. rewrite IHq. simpl. f_equal; lia.
  - apply iter_eq. exact IHb.
Qed.

(** Time is at least the amount added. *)
Theorem cost_ge_gain : forall p, gain p <= cost p.
Proof.
  induction p as [| p IHp q IHq | k b IHb]; simpl.
  - lia.
  - lia.
  - assert (k * gain b <= k * (cost b + 1)) by (apply Nat.mul_le_mono_l; lia). lia.
Qed.

(** A time-optimal program contains no loop. *)
Theorem time_optimal_is_loop_free : forall p, cost p = gain p -> loopFree p = true.
Proof.
  induction p as [| p IHp q IHq | k b IHb]; simpl; intros H.
  - reflexivity.
  - pose proof (cost_ge_gain p). pose proof (cost_ge_gain q).
    rewrite IHp by lia. rewrite IHq by lia. reflexivity.
  - pose proof (cost_ge_gain b).
    assert (k * gain b <= k * (cost b + 1)) by (apply Nat.mul_le_mono_l; lia). lia.
Qed.

(** In the loop-free fragment, size, time and gain coincide. *)
Theorem loopFree_size_eq_cost : forall p, loopFree p = true -> size p = cost p /\ size p = gain p.
Proof.
  induction p as [| p IHp q IHq | k b IHb]; simpl; intros H.
  - split; reflexivity.
  - apply andb_prop in H. destruct H as [H1 H2].
    destruct (IHp H1). destruct (IHq H2). split; lia.
  - discriminate.
Qed.

(** Every fastest program for [v |-> v + k] has size exactly [k]. *)
Theorem fastest_programs_have_size_k : forall p k, gain p = k -> cost p = k -> size p = k.
Proof.
  intros p k Hg Hc.
  destruct (loopFree_size_eq_cost p (time_optimal_is_loop_free p ltac:(lia))). lia.
Qed.

Fixpoint unroll (m : nat) : Prog :=
  match m with
  | 0 => Inc
  | S m' => Seq Inc (unroll m')
  end.

Theorem unroll_spec : forall m,
  gain (unroll m) = m + 1 /\ cost (unroll m) = m + 1 /\ size (unroll m) = m + 1.
Proof.
  induction m as [| m IH]; simpl.
  - repeat split.
  - destruct IH as [A [B C]]. repeat split; lia.
Qed.

Theorem loop_inc_size : forall k,
  gain (Loop k Inc) = k /\ cost (Loop k Inc) = 2 * k + 1 /\ size (Loop k Inc) = bits k + 2.
Proof. intros k. simpl. repeat split; lia. Qed.

(** Time can be exponential in description length. *)
Theorem loop_inc_exponential_gap : forall k, 1 <= k ->
  2 ^ size (Loop k Inc) <= 4 * cost (Loop k Inc).
Proof.
  intros k Hk. destruct (bits_spec k Hk) as [H1 H2].
  destruct (loop_inc_size k) as [_ [Hc Hs]]. rewrite Hc, Hs.
  replace (bits k + 2) with (S (S (bits k))) by lia.
  rewrite !Nat.pow_succ_r'. lia.
Qed.

Theorem small_lt_pow : forall m, 4 <= m -> 2 * m + 4 < 2 ^ m.
Proof.
  induction m as [| m IH]; intros Hm.
  - lia.
  - rewrite Nat.pow_succ_r'.
    destruct (Nat.eq_dec m 3) as [E | E].
    + subst m. simpl. lia.
    + specialize (IH ltac:(lia)). lia.
Qed.

Theorem loop_inc_short : forall k, 6 <= k -> size (Loop k Inc) < k.
Proof.
  intros k Hk. destruct (bits_spec k ltac:(lia)) as [H1 H2].
  destruct (loop_inc_size k) as [_ [_ Hs]]. rewrite Hs.
  destruct (Nat.lt_ge_cases (bits k + 2) k) as [L | L]; [exact L |].
  exfalso.
  assert (Hp : 2 ^ (k - 2) <= 2 ^ bits k) by (apply Nat.pow_le_mono_r; lia).
  pose proof (small_lt_pow (k - 2) ltac:(lia)). lia.
Qed.

(** Main refutation: for every k >= 6, any program for [v |-> v + k] that is
    no longer than [Loop k Inc] is strictly slower than the fastest one. *)
Theorem shortest_is_never_fastest : forall k q, 6 <= k ->
  gain q = k -> size q <= size (Loop k Inc) -> cost (unroll (k - 1)) < cost q.
Proof.
  intros k q Hk Hq Hs.
  pose proof (loop_inc_short k Hk) as Hshort.
  destruct (unroll_spec (k - 1)) as [_ [Hu _]].
  pose proof (cost_ge_gain q) as Hge.
  assert (Hne : cost q <> k).
  { intros Hc. pose proof (fastest_programs_have_size_k q k Hq Hc). lia. }
  lia.
Qed.

Definition SameFunction (p q : Prog) : Prop := forall v, fst (run p v) = fst (run q v).

Theorem shorter_not_implies_faster :
  ~ (forall p q, SameFunction p q -> size p <= size q -> cost p <= cost q).
Proof.
  intros H.
  assert (Hsame : SameFunction (Loop 6 Inc) (unroll 5)).
  { intros v. rewrite !run_eq. simpl. lia. }
  pose proof (loop_inc_short 6 ltac:(lia)) as Hs.
  destruct (unroll_spec 5) as [_ [Hc Hz]].
  specialize (H _ _ Hsame ltac:(lia)).
  destruct (loop_inc_size 6) as [_ [Hc6 _]]. lia.
Qed.

Theorem faster_not_implies_shorter :
  ~ (forall p q, SameFunction p q -> cost p <= cost q -> size p <= size q).
Proof.
  intros H.
  assert (Hsame : SameFunction (unroll 5) (Loop 6 Inc)).
  { intros v. rewrite !run_eq. simpl. lia. }
  pose proof (loop_inc_short 6 ltac:(lia)) as Hs.
  destruct (unroll_spec 5) as [_ [Hc Hz]].
  destruct (loop_inc_size 6) as [_ [Hc6 _]].
  specialize (H _ _ Hsame ltac:(lia)). lia.
Qed.

Theorem padding_longer_and_slower : forall k,
  SameFunction (Loop k Inc) (Seq (Loop k Inc) (Loop 0 Inc)) /\
  size (Loop k Inc) < size (Seq (Loop k Inc) (Loop 0 Inc)) /\
  cost (Loop k Inc) < cost (Seq (Loop k Inc) (Loop 0 Inc)).
Proof.
  intros k. split; [| split].
  - intros v. rewrite !run_eq. simpl. lia.
  - simpl. lia.
  - simpl. lia.
Qed.

(** * Part B: Levin universal search *)

Section Levin.
Context {W : Type}.

Definition MonotoneRuns (runs : nat -> nat -> option W) : Prop :=
  forall i t t' w, t <= t' -> runs i t = Some w -> runs i t' = Some w.

Definition check (V : W -> bool) (o : option W) : option W :=
  match o with
  | Some w => if V w then Some w else None
  | None => None
  end.

Fixpoint phaseAux (runs : nat -> nat -> option W) (V : W -> bool) (j m : nat) : option W :=
  match m with
  | 0 => None
  | S i =>
      match phaseAux runs V j i with
      | Some w => Some w
      | None => check V (runs i (2 ^ (j - i)))
      end
  end.

Definition phase (runs : nat -> nat -> option W) (V : W -> bool) (j : nat) : option W :=
  phaseAux runs V j (S j).

Fixpoint search (runs : nat -> nat -> option W) (V : W -> bool) (J : nat) : option W :=
  match J with
  | 0 => phase runs V 0
  | S J' =>
      match search runs V J' with
      | Some w => Some w
      | None => phase runs V (S J')
      end
  end.

Fixpoint phaseWorkAux (j m : nat) : nat :=
  match m with
  | 0 => 0
  | S i => phaseWorkAux j i + 2 ^ (j - i)
  end.

Definition phaseWork (j : nat) : nat := phaseWorkAux j (S j).

Fixpoint totalWork (J : nat) : nat :=
  match J with
  | 0 => phaseWork 0
  | S J' => totalWork J' + phaseWork (S J')
  end.

Theorem check_sound : forall V o w, check V o = Some w -> V w = true.
Proof.
  intros V o w H. destruct o as [u |]; simpl in H; [| discriminate].
  destruct (V u) eqn:E; [| discriminate]. injection H as <-. exact E.
Qed.

Theorem phaseAux_sound : forall runs V j m w, phaseAux runs V j m = Some w -> V w = true.
Proof.
  intros runs V j m. induction m as [| m IH]; intros w H; simpl in H; [discriminate |].
  destruct (phaseAux runs V j m) as [u |] eqn:E.
  - injection H as <-. exact (IH u eq_refl).
  - exact (check_sound V _ w H).
Qed.

(** Soundness: whatever Levin search returns is verified. *)
Theorem search_sound : forall runs V J w, search runs V J = Some w -> V w = true.
Proof.
  intros runs V J. induction J as [| J IH]; intros w H; simpl in H.
  - exact (phaseAux_sound runs V 0 1 w H).
  - destruct (search runs V J) as [u |] eqn:E.
    + injection H as <-. exact (IH u eq_refl).
    + exact (phaseAux_sound runs V (S J) (S (S J)) w H).
Qed.

Theorem phaseAux_finds : forall runs V j i w,
  check V (runs i (2 ^ (j - i))) = Some w ->
  forall m, i < m -> exists w', phaseAux runs V j m = Some w'.
Proof.
  intros runs V j i w Hi m. induction m as [| m IH]; intros Hm; [lia |].
  simpl. destruct (phaseAux runs V j m) as [u |] eqn:E.
  - exists u. reflexivity.
  - destruct (Nat.eq_dec i m) as [-> | Ne].
    + exists w. exact Hi.
    + destruct (IH ltac:(lia)) as [u Hu]. discriminate.
Qed.

Theorem search_mono : forall runs V j w, phase runs V j = Some w ->
  forall J, j <= J -> exists w', search runs V J = Some w'.
Proof.
  intros runs V j w Hj J. induction J as [| J IH]; intros HJ.
  - assert (j = 0) by lia. subst j. exists w. exact Hj.
  - simpl. destruct (search runs V J) as [u |] eqn:E.
    + exists u. reflexivity.
    + destruct (Nat.eq_dec j (S J)) as [-> | Ne].
      * exists w. exact Hj.
      * destruct (IH ltac:(lia)) as [u Hu]. discriminate.
Qed.

(** Completeness: a verified output of program [i] within [t <= 2^L] steps
    is found (or another verified witness is) by phase [i + L]. *)
Theorem levin_finds : forall runs V, MonotoneRuns runs ->
  forall i t L w, runs i t = Some w -> V w = true -> t <= 2 ^ L ->
  exists w', search runs V (i + L) = Some w' /\ V w' = true.
Proof.
  intros runs V Hmono i t L w Hrun HV HL.
  assert (Hr : runs i (2 ^ (i + L - i)) = Some w).
  { replace (i + L - i) with L by lia. exact (Hmono i t (2 ^ L) w HL Hrun). }
  assert (Hc : check V (runs i (2 ^ (i + L - i))) = Some w).
  { rewrite Hr. simpl. rewrite HV. reflexivity. }
  destruct (phaseAux_finds runs V (i + L) i w Hc (S (i + L)) ltac:(lia)) as [w1 Hw1].
  destruct (search_mono runs V (i + L) w1 Hw1 (i + L) (le_n _)) as [w2 Hw2].
  exists w2. split; [exact Hw2 | exact (search_sound runs V (i + L) w2 Hw2)].
Qed.

Theorem phaseWorkAux_eq : forall j i, i <= S j -> phaseWorkAux j i + 2 ^ (S j - i) = 2 ^ (S j).
Proof.
  intros j i. induction i as [| i IH]; intros H; simpl phaseWorkAux.
  - rewrite Nat.sub_0_r. reflexivity.
  - specialize (IH ltac:(lia)).
    replace (S j - i) with (S (j - i)) in IH by lia.
    replace (S j - S i) with (j - i) by lia.
    rewrite Nat.pow_succ_r' in IH. lia.
Qed.

Theorem phaseWork_eq : forall j, phaseWork j + 1 = 2 ^ (S j).
Proof.
  intros j. unfold phaseWork. pose proof (phaseWorkAux_eq j (S j) (le_n _)) as H.
  rewrite Nat.sub_diag in H. simpl (2 ^ 0) in H. exact H.
Qed.

(** Total simulated work through phase [J] is below [2 ^ (J + 2)]. *)
Theorem totalWork_lt : forall J, totalWork J + 1 < 2 ^ (J + 2).
Proof.
  induction J as [| J IH].
  - simpl. unfold phaseWork. simpl. lia.
  - simpl totalWork. pose proof (phaseWork_eq (S J)) as H.
    replace (S J + 2) with (S (J + 2)) by lia.
    replace (S (S J)) with (J + 2) in H by lia.
    rewrite Nat.pow_succ_r'. lia.
Qed.

Theorem exists_ceil_log : forall t, 1 <= t -> exists L, t <= 2 ^ L /\ 2 ^ L < 2 * t.
Proof.
  induction t as [| t IH]; intros Ht; [lia |].
  destruct (Nat.eq_dec t 0) as [-> | Ne].
  - exists 0. simpl. lia.
  - destruct (IH ltac:(lia)) as [L [H1 H2]].
    destruct (Nat.le_gt_cases (S t) (2 ^ L)) as [H3 | H3].
    + exists L. split; lia.
    + exists (S L). rewrite Nat.pow_succ_r'. split; lia.
Qed.

(** Quantitative Levin bound: total work below [8 * 2^i * t]. *)
Theorem levin_search_bound : forall runs V, MonotoneRuns runs ->
  forall i t w, 1 <= t -> runs i t = Some w -> V w = true ->
  exists J w', search runs V J = Some w' /\ V w' = true /\ totalWork J < 8 * 2 ^ i * t.
Proof.
  intros runs V Hmono i t w Ht Hrun HV.
  destruct (exists_ceil_log t Ht) as [L [H1 H2]].
  destruct (levin_finds runs V Hmono i t L w Hrun HV H1) as [w' [Hs Hv]].
  exists (i + L), w'. split; [exact Hs | split; [exact Hv |]].
  pose proof (totalWork_lt (i + L)) as Hw.
  assert (E : 2 ^ (i + L + 2) = 4 * (2 ^ i * 2 ^ L)).
  { rewrite !Nat.pow_add_r. simpl (2 ^ 2). lia. }
  assert (Hm : 2 ^ i * 2 ^ L < 2 ^ i * (2 * t)).
  { apply Nat.mul_lt_mono_pos_l; [| exact H2].
    pose proof (Nat.pow_le_mono_r 2 0 i ltac:(lia) ltac:(lia)). simpl in H. lia. }
  assert (E2 : 8 * 2 ^ i * t = 4 * (2 ^ i * (2 * t))).
  { rewrite (Nat.mul_comm 2 t), Nat.mul_assoc. lia. }
  lia.
Qed.

End Levin.

(** * Instance-indexed Levin search and the open obligation *)

(** Open obligation (not assumed anywhere): one program index [i] finds a
    verified witness within [c * n^d + c] steps on every satisfiable
    instance of size [n].  For SAT this is equivalent to P = NP. *)
Definition PolyTimeWitnessProgramExists {X W : Type} (sz : X -> nat)
  (runs : nat -> X -> nat -> option W) (V : X -> W -> bool) : Prop :=
  exists i c d, forall x, (exists w, V x w = true) ->
    exists t w, t <= c * sz x ^ d + c /\ runs i x t = Some w /\ V x w = true.

(** Conditional theorem: under the obligation, Levin search is polynomial on
    every satisfiable instance with the fixed factor [K = 8 * 2^i]. *)
Theorem levin_poly_of_obligation : forall {X W : Type} (sz : X -> nat)
  (runs : nat -> X -> nat -> option W) (V : X -> W -> bool),
  (forall x, MonotoneRuns (fun i t => runs i x t)) ->
  PolyTimeWitnessProgramExists sz runs V ->
  exists K c d, forall x, (exists w, V x w = true) ->
    exists J w, search (fun i t => runs i x t) (V x) J = Some w /\ V x w = true /\
      totalWork J < K * (c * sz x ^ d + c + 1).
Proof.
  intros X W sz runs V Hmono [i [c [d H]]].
  exists (8 * 2 ^ i), c, d. intros x Hx.
  destruct (H x Hx) as [t [w [Ht [Hr Hv]]]].
  assert (Hr' : runs i x (t + 1) = Some w) by exact (Hmono x i t (t + 1) w ltac:(lia) Hr).
  destruct (levin_search_bound (fun i t => runs i x t) (V x) (Hmono x) i (t + 1) w
              ltac:(lia) Hr' Hv) as [J [w' [Hs [Hv' Hw]]]].
  exists J, w'. split; [exact Hs | split; [exact Hv' |]].
  assert (8 * 2 ^ i * (t + 1) <= 8 * 2 ^ i * (c * sz x ^ d + c + 1))
    by (apply Nat.mul_le_mono_l; lia).
  lia.
Qed.
