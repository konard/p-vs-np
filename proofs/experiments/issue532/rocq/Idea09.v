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
   < 2^(J+2), the bound totalWork < 8 * 2^i * t, and the schema theorem
   levin_poly_for over abstract runs (PolyTimeWitnessProgramExistsFor).

   Part C: the obligation in the shared machine model (Machines.v).  The
   open obligation is SATWitnessMachine: one Machine computes (Computes m f p)
   a satisfying assignment of every satisfiable encoded formula.  It gives
   InP SAT and, with SATHard, PEqualsNP, using the known composition theorem
   WitnessCheckInP as an explicit premise.  Levin search over an enumeration
   of machines (machineRuns) is polynomial under the obligation.

   Differences from Lean: Rocq has no function extensionality and this file
   uses no classical logic.  The output reader machineRuns is a computable
   step-bounded interpreter (exitWithin, readOutput) where Lean uses
   classical choice; the non-vacuity theorem diagonalises directly against
   the computable clocked language outputsTrue (indexed by machine and
   polynomial) instead of applying the Cantor lemma to the classical
   outputsTrue of Lean.  The exported statements are the same.

   Nothing here proves or refutes P = NP. *)

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

(** * Instance-indexed Levin search: the abstract schema *)

(** Schema (abstract [runs], not the obligation of this file): one program
    index [i] finds a verified witness within [c * n^d + c] steps on every
    satisfiable instance of size [n].  The machine-model statement is
    [SATWitnessMachine] below. *)
Definition PolyTimeWitnessProgramExistsFor {X W : Type} (sz : X -> nat)
  (runs : nat -> X -> nat -> option W) (V : X -> W -> bool) : Prop :=
  exists i c d, forall x, (exists w, V x w = true) ->
    exists t w, t <= c * sz x ^ d + c /\ runs i x t = Some w /\ V x w = true.

(** Schema theorem: under the schema, Levin search is polynomial on every
    satisfiable instance with the fixed factor [K = 8 * 2^i]. *)
Theorem levin_poly_for : forall {X W : Type} (sz : X -> nat)
  (runs : nat -> X -> nat -> option W) (V : X -> W -> bool),
  (forall x, MonotoneRuns (fun i t => runs i x t)) ->
  PolyTimeWitnessProgramExistsFor sz runs V ->
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

(** * Part C: the obligation in the shared machine model *)

From Stdlib Require Import List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** The SAT verifier: the word [w], read as an assignment, satisfies the
    formula encoded by [x]. *)
Definition satCheck (x w : Word) : bool := evalCNF (toAssign w) (decode x).

(** [SAT] is exactly the set of words that have a [satCheck] witness. *)
Theorem sat_iff_exists_witness : forall x : Word,
  SAT x = true <-> exists w, satCheck x w = true.
Proof.
  intro x. rewrite sat_iff. split.
  - intros [a ha]. exists (prefixOf a (numVars (decode x))). unfold satCheck.
    rewrite (evalCNF_congr (toAssign (prefixOf a (numVars (decode x)))) a
               (numVars (decode x)) (decode x)).
    + exact ha.
    + intros i hi. apply toAssign_prefixOf. exact hi.
    + apply varsBelow_numVars.
  - intros [w hw]. exists (toAssign w). exact hw.
Qed.

(** A single machine that, in polynomial time, outputs a [V]-witness for
    every [x] that has one. *)
Definition PolyWitnessMachine (V : Word -> Word -> bool) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, (exists w, V x w = true) -> V x (f x) = true.

(** Open obligation.  One [Machine] outputs, within a polynomial number of
    [Reaches] steps, a satisfying assignment of every satisfiable encoded
    formula.  This is the machine-model form of "one fixed program finds SAT
    witnesses in polynomial time", the condition under which Levin search
    is polynomial.  It is not proved or refuted here. *)
Definition SATWitnessMachine : Prop := PolyWitnessMachine satCheck.

(** Known theorem, not mechanised here: if [m] computes [f] in polynomial
    time, then checking the SAT verifier on [(x, f x)] is in P: copy [x], run
    [m] on the copy, then evaluate the formula [decode x] under the
    assignment [f x], all in time polynomial in [|x|] (the output [f x] has
    polynomial length by [computes_output_poly]).  This is the closure of P
    under composition with polynomial-time functions, using the polynomial
    simulation of multi-tape by single-tape machines: Sipser, Introduction to
    the Theory of Computation, 3rd ed. (2013), Theorem 7.8; Arora and Barak,
    Computational Complexity: A Modern Approach (2009), Chapter 1.  It is
    used only as an explicit premise. *)
Definition WitnessCheckInP : Prop :=
  forall (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p ->
    InP (fun x => satCheck x (f x)).

(** Conditional theorem: the open obligation (with the known composition
    theorem) puts [SAT] in P. *)
Theorem inP_sat_of_witnessMachine : WitnessCheckInP -> SATWitnessMachine -> InP SAT.
Proof.
  intros hC [m [f [p [hm hf]]]].
  apply (inP_ext (fun x => satCheck x (f x))); [| exact (hC m f p hm)].
  intro x. destruct (SAT x) eqn:hs.
  - exact (hf x (proj1 (sat_iff_exists_witness x) hs)).
  - destruct (satCheck x (f x)) eqn:hw; [| reflexivity].
    assert (h : SAT x = true) by (apply sat_iff_exists_witness; exists (f x); exact hw).
    rewrite hs in h. discriminate h.
Qed.

(** Conditional theorem: the open obligation, the composition theorem and
    the NP-hardness half of Cook-Levin ([SATHard]) give P = NP. *)
Theorem pEqualsNP_of_witnessMachine :
  WitnessCheckInP -> SATHard -> SATWitnessMachine -> PEqualsNP.
Proof.
  intros hC hard h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_witnessMachine hC h)).
Qed.

(** ** A computable output reader

    Lean reads a machine's output with classical choice.  Rocq uses a
    step-bounded interpreter: [exitWithin m c fuel] follows at most [fuel]
    non-halting steps from [c] until the exit state [length (program m)],
    and [readOutput] reads [map ofBool w ++ blanks k] off a tape whose head
    is on the leftmost cell. *)

Fixpoint exitWithin (m : Machine) (c : Config) (fuel : nat) : option Config :=
  if Nat.eqb (state c) (length (program m)) then Some c else
  match fuel with
  | 0 => None
  | S f => match step m c with
           | inl _ => None
           | inr c' => exitWithin m c' f
           end
  end.

Theorem exitWithin_of_reaches : forall m c s d, Reaches m c s d ->
  state d = length (program m) -> forall fuel, s <= fuel -> exitWithin m c fuel = Some d.
Proof.
  intros m c s d h. induction h as [c | c c' d t hs hr IH]; intros hd fuel hf.
  - destruct fuel; simpl; rewrite (proj2 (Nat.eqb_eq _ _) hd); reflexivity.
  - destruct fuel as [| fuel]; [lia |].
    pose proof (state_lt_of_step _ _ _ hs) as hlt.
    assert (hne : Nat.eqb (state c) (length (program m)) = false)
      by (apply Nat.eqb_neq; lia).
    simpl. rewrite hne, hs.
    apply IH; [exact hd | lia].
Qed.

Theorem reaches_of_exitWithin : forall m fuel c d, exitWithin m c fuel = Some d ->
  exists s, s <= fuel /\ Reaches m c s d /\ state d = length (program m).
Proof.
  intros m fuel. induction fuel as [| fuel IH]; intros c d h; simpl in h;
    destruct (Nat.eqb (state c) (length (program m))) eqn:he.
  - injection h as <-. exists 0. split; [lia |].
    split; [apply reaches_refl | apply Nat.eqb_eq; exact he].
  - discriminate h.
  - injection h as <-. exists 0. split; [lia |].
    split; [apply reaches_refl | apply Nat.eqb_eq; exact he].
  - destruct (step m c) as [b | c'] eqn:hs; [discriminate h |].
    destruct (IH c' d h) as [s [hs' [hr hd]]].
    exists (S s). split; [lia | split; [apply reaches_next with c'; assumption | exact hd]].
Qed.

Definition isBlank (a : Symbol) : bool := match a with blank => true | _ => false end.

(** Read [map ofBool w ++ blanks k] back as [w]. *)
Fixpoint readBits (l : list Symbol) : option Word :=
  match l with
  | [] => Some []
  | zero :: r => option_map (cons false) (readBits r)
  | one :: r => option_map (cons true) (readBits r)
  | blank :: r => if forallb isBlank r then Some [] else None
  | separator :: _ => None
  end.

Theorem readBits_bits : forall w k, readBits (map ofBool w ++ blanks k) = Some w.
Proof.
  induction w as [| b w IH]; intro k.
  - destruct k as [| k]; [reflexivity |]. simpl.
    assert (h : forallb isBlank (repeat blank k) = true)
      by (induction k as [| k IHk]; [reflexivity | exact IHk]).
    rewrite h. reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Theorem blanks_of_forallb : forall l, forallb isBlank l = true -> l = blanks (length l).
Proof.
  induction l as [| a l IH]; intro h; [reflexivity |].
  simpl in h. apply andb_prop in h. destruct h as [ha h].
  destruct a; try discriminate ha. unfold blanks. simpl. f_equal. exact (IH h).
Qed.

Theorem bits_of_readBits : forall l w, readBits l = Some w ->
  exists k, l = map ofBool w ++ blanks k.
Proof.
  induction l as [| a l IH]; intros w h.
  - injection h as <-. exists 0. reflexivity.
  - destruct a; simpl in h.
    + destruct (forallb isBlank l) eqn:hb; [| discriminate h].
      injection h as <-. exists (S (length l)). simpl.
      rewrite (blanks_of_forallb l hb). unfold blanks. rewrite repeat_length.
      reflexivity.
    + destruct (readBits l) as [v |] eqn:hr; [| discriminate h].
      injection h as <-. destruct (IH v eq_refl) as [k hk].
      exists k. rewrite hk. reflexivity.
    + destruct (readBits l) as [v |] eqn:hr; [| discriminate h].
      injection h as <-. destruct (IH v eq_refl) as [k hk].
      exists k. rewrite hk. reflexivity.
    + discriminate h.
Qed.

Definition readOutput (c : Config) : option Word :=
  match tapeLeft c with
  | [] => readBits (tapeHead c :: tapeRight c)
  | _ :: _ => None
  end.

(** The output of [m] on [x] if it exits within [t] steps. *)
Definition outputFor (m : Machine) (x : Word) (t : nat) : option Word :=
  obind (exitWithin m (initial x) t) readOutput.

(** ** Non-vacuity *)

(** The language "[m] outputs [[true]] on [w] within [p(|w|)] steps".  Lean
    uses the classical [decide] of "some function computed by [m] maps [w]
    to [[true]]"; this clocked version is computable. *)
Definition outputsTrue (x : Machine * Polynomial) : Language := fun w =>
  match outputFor (fst x) w (evalPoly (snd x) (length w)) with
  | Some [true] => true
  | _ => false
  end.

(** The diagonal against [outputsTrue]. *)
Definition witnessDiag : Language := fun w =>
  match decMachinePoly w with
  | Some x => negb (outputsTrue x w)
  | None => true
  end.

(** The verifier "[w = [L x]]". *)
Definition singletonCheck (L : Language) (x w : Word) : bool :=
  match w with
  | [b] => Bool.eqb b (L x)
  | _ => false
  end.

(** Non-vacuity: [PolyWitnessMachine] is not a property of every verifier.
    For the verifier "[w = [L x]]" a witness machine computes [L], and no
    machine computes the diagonal [witnessDiag]. *)
Theorem not_forall_polyWitnessMachine : ~ (forall V : Word -> Word -> bool, PolyWitnessMachine V).
Proof.
  intro hall.
  destruct (hall (singletonCheck witnessDiag)) as [m [f [p [hm hf]]]].
  set (w := encMachinePoly (m, p)).
  assert (hfw : f w = [witnessDiag w]).
  { assert (h : singletonCheck witnessDiag w (f w) = true).
    { apply hf. exists [witnessDiag w]. simpl. apply Bool.eqb_reflx. }
    unfold singletonCheck in h. destruct (f w) as [| b [| b' r]]; try discriminate h.
    apply Bool.eqb_prop in h. rewrite h. reflexivity. }
  destruct (hm w) as [t [c [ht [hr [hcs [hcl [k hck]]]]]]].
  assert (ho : outputsTrue (m, p) w = witnessDiag w).
  { unfold outputsTrue, outputFor. simpl fst. simpl snd.
    rewrite (exitWithin_of_reaches _ _ _ _ hr hcs _ ht). simpl.
    unfold readOutput. rewrite hcl, hck, readBits_bits, hfw.
    destruct (witnessDiag w); reflexivity. }
  assert (hd : witnessDiag w = negb (outputsTrue (m, p) w)).
  { unfold witnessDiag at 1. unfold w at 1. rewrite decMachinePoly_encMachinePoly.
    reflexivity. }
  rewrite ho in hd. destruct (witnessDiag w); discriminate hd.
Qed.

(** ** Levin search over machines

    [OutputsWithin m x t w]: machine [m] started on [x] reaches its exit
    state with output [w] within [t] steps.  [machineRuns e] feeds this into
    the Levin schema for an enumeration [e] of machines. *)

(** Machine [m] on input [x] exits with output [w] within [t] [Reaches]
    steps. *)
Definition OutputsWithin (m : Machine) (x : Word) (t : nat) (w : Word) : Prop :=
  exists s c k, s <= t /\ Reaches m (initial x) s c /\ state c = length (program m) /\
    tapeLeft c = [] /\ tapeHead c :: tapeRight c = map ofBool w ++ blanks k.

Theorem outputsWithin_unique : forall m x t t' w w',
  OutputsWithin m x t w -> OutputsWithin m x t' w' -> w = w'.
Proof.
  intros m x t t' w w' [s [c [k [_ [hc [hcs [_ hck]]]]]]] [s' [d [l [_ [hd [hds [_ hdl]]]]]]].
  pose proof (reaches_exit_unique _ _ _ _ _ _ hc hd hcs hds). subst d.
  rewrite hck in hdl. exact (map_ofBool_blanks_injective _ _ _ _ hdl).
Qed.

(** The [runs] of Levin's schema for the machine enumeration [e]: the output
    of machine [e i] on [x] if it exits within [t] steps (computable, where
    Lean uses classical choice). *)
Definition machineRuns (e : nat -> Machine) (i : nat) (x : Word) (t : nat) : option Word :=
  outputFor (e i) x t.

Theorem machineRuns_eq : forall e i x t w,
  OutputsWithin (e i) x t w -> machineRuns e i x t = Some w.
Proof.
  intros e i x t w [s [c [k [hs [hr [hcs [hcl hck]]]]]]].
  unfold machineRuns, outputFor.
  rewrite (exitWithin_of_reaches _ _ _ _ hr hcs _ hs). simpl.
  unfold readOutput. rewrite hcl, hck. apply readBits_bits.
Qed.

Theorem machineRuns_spec : forall e i x t w,
  machineRuns e i x t = Some w -> OutputsWithin (e i) x t w.
Proof.
  intros e i x t w h. unfold machineRuns, outputFor in h.
  destruct (exitWithin (e i) (initial x) t) as [c |] eqn:he; [| discriminate h].
  simpl in h. destruct (reaches_of_exitWithin _ _ _ _ he) as [s [hs [hr hcs]]].
  unfold readOutput in h. destruct (tapeLeft c) as [| a l] eqn:hl; [| discriminate h].
  destruct (bits_of_readBits _ _ h) as [k hk].
  exists s, c, k. auto.
Qed.

Theorem machineRuns_monotone : forall e x, MonotoneRuns (fun i t => machineRuns e i x t).
Proof.
  intros e x i t t' w htt' h.
  destruct (machineRuns_spec e i x t w h) as [s [c [k [hs hr]]]].
  apply machineRuns_eq. exists s, c, k. split; [lia | exact hr].
Qed.

(** Levin search over machines: under the open obligation, for any
    enumeration [e] that lists every machine, Levin search with the SAT
    verifier finds a satisfying assignment of every satisfiable [x] with
    total simulated work below [K * (p(|x|) + 1)] for a constant [K].  The
    simulated work counts [Reaches] steps of the enumerated machines; the
    overhead of a universal simulator and of the verifier calls is not
    counted here. *)
Theorem levin_sat_of_witnessMachine : forall e : nat -> Machine,
  (forall m, exists i, e i = m) -> SATWitnessMachine ->
  exists (K : nat) (p : Polynomial), forall x, SAT x = true ->
    exists J w, search (fun i t => machineRuns e i x t) (satCheck x) J = Some w /\
      satCheck x w = true /\ totalWork J < K * (evalPoly p (length x) + 1).
Proof.
  intros e he [m [f [p [hm hf]]]].
  destruct (he m) as [i hi].
  exists (8 * 2 ^ i), p. intros x hx.
  pose proof (hf x (proj1 (sat_iff_exists_witness x) hx)) as hv.
  destruct (hm x) as [t [c [ht [hr [hcs [hcl [k hck]]]]]]].
  assert (hrun : machineRuns e i x (evalPoly p (length x) + 1) = Some (f x)).
  { apply machineRuns_eq. rewrite hi. exists t, c, k.
    split; [lia | auto]. }
  exact (levin_search_bound (fun i t => machineRuns e i x t) (satCheck x)
    (machineRuns_monotone e x) i (evalPoly p (length x) + 1) (f x) ltac:(lia) hrun hv).
Qed.
