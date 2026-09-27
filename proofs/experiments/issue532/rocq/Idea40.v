(* Issue #532, Idea 40: size-uniform invariant (induction with resource bounds).

   Rocq counterpart of ../lean/Idea40.lean (same theorem names and content).
   Additive recurrences T(n+1) <= T(n) + q(n) with q monotone give
   T(n) <= c + n * q(n), polynomial when q is (additive_bound, additive_poly);
   doubling/branching recurrences give 2^n (doubling_exact, branching_lower), which
   beats every polynomial (poly_lt_two_pow, branching_not_poly,
   branchCost_exponential). A self-reduction with one same-answer call and
   polynomial step cost gives a correct polynomial-cost solver (schema
   AdditiveSelfReductionFor, poly_solver_for, self_reduction_solver_bound;
   abstract costs).

   Machine model (Machines.v, time = Run step count): the open obligation
   SATMachineSelfReduction (= MachineSelfReductionOf SAT) asks for a
   polynomial-time machine step map (Computes) that never lengthens the word,
   removes one variable (satSize) and keeps SAT, plus a machine deciding SAT
   on variable-free formulas (DecidesOn).  inP_sat_of_machineSelfReduction and
   pEqualsNP_of_machineSelfReduction derive InP SAT and PEqualsNP from the
   known theorem IterationClosure (and SATHard), both explicit premises.
   not_forall_machineSelfReductionOf shows the machine predicate is not
   satisfied by every language.

   Rocq differences from Lean: mapOf and acceptsOf are computable
   step-bounded interpreters indexed by a machine and an explicit polynomial
   clock (Lean chooses them classically from the machine alone), so
   selfReductionLanguage is indexed by ((m, p), (d, q)); machineSelfReductionOf_eq
   is pointwise (no function extensionality), and non-vacuity is a direct
   diagonal over encPair codes (selfReductionDiag) instead of the Cantor
   family lemma.  All proofs are constructive. *)

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

(* Self-reduction with one call: the schema (abstract costs). *)

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

(** Schema (abstract, no machine model): an additive-cost self-reduction for
    the predicate [answer].  Size-0 instances are answered by [base] (cost at
    most [c]), and one step maps a size-(n+1) instance to a size-n instance
    with the same answer at polynomial cost.  The costs here are free
    functions, so this schema is only the bookkeeping part of the idea; the
    statement about real machines is [SATMachineSelfReduction] below. *)
Definition AdditiveSelfReductionFor {Inst : Type} (size : Inst -> nat) (answer : Inst -> bool)
    : Prop :=
  exists (base : Inst -> bool) (step : Inst -> Inst) (baseCost stepCost : Inst -> nat)
         (c a k : nat),
    (forall I, size I = 0 -> base I = answer I) /\ (forall I, baseCost I <= c) /\
    (forall I n, size I = n + 1 -> size (step I) = n /\ answer (step I) = answer I) /\
    (forall I, stepCost I <= a * (size I + 1) ^ k).

(** Schema theorem: data meeting [AdditiveSelfReductionFor] yield a correct
    solver whose (abstract) cost is polynomial in the size. *)
Theorem poly_solver_for {Inst : Type} (size : Inst -> nat)
    (answer : Inst -> bool) :
  AdditiveSelfReductionFor size answer ->
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

(* Explicit solver bound: for any data meeting the conditions of AdditiveSelfReductionFor,
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

(* ---------- The machine model: one-call self-reduction for SAT ---------- *)

(* From here on the cost is the step count of a Machine run.  SAT is the
   shared-model language on words, and the size of a word is the number of
   variables of the formula it denotes, numVars (decode x). *)

From Stdlib Require Import List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** Size of a word for the self-reduction: the number of variables of the
    formula it denotes (0 for variable-free formulas). *)
Definition satSize (x : Word) : nat := numVars (decode x).

Theorem clauseBound_append : forall (cur : Clause) (l : Lit),
  clauseBound (cur ++ [l]) = Nat.max (clauseBound cur) (var l + 1).
Proof.
  intros cur l. induction cur as [| l' c IH]; cbn [app clauseBound]; [lia |].
  rewrite IH. lia.
Qed.

Theorem numVars_decodeAux_le : forall (w : list bool) (k : nat) (cur : Clause),
  numVars (decodeAux w k cur) <= Nat.max (clauseBound cur) (k + length w).
Proof.
  assert (H : forall n w k cur, length w <= n ->
    numVars (decodeAux w k cur) <= Nat.max (clauseBound cur) (k + length w)).
  { intro n. induction n as [| n IH]; intros w k cur hn.
    - destruct w; [cbn [decodeAux numVars]; lia | cbn [length] in hn; lia].
    - destruct w as [| a w]; [cbn [decodeAux numVars]; lia |].
      destruct w as [| b rest]; [destruct a; cbn [decodeAux numVars]; lia |].
      cbn [length] in hn |- *.
      destruct a, b; cbn [decodeAux numVars].
      + pose proof (IH rest (S k) cur ltac:(lia)). lia.
      + pose proof (IH rest 0 [] ltac:(lia)) as h. cbn [clauseBound] in h. lia.
      + pose proof (IH rest 0 (cur ++ [mkLit k true]) ltac:(lia)) as h.
        rewrite clauseBound_append in h. cbn [var] in h. lia.
      + pose proof (IH rest 0 (cur ++ [mkLit k false]) ltac:(lia)) as h.
        rewrite clauseBound_append in h. cbn [var] in h. lia. }
  intros w k cur. exact (H (length w) w k cur (le_n _)).
Qed.

(** A word of length n denotes a formula with at most n variables. *)
Theorem satSize_le_length : forall x : Word, satSize x <= length x.
Proof.
  intro x. pose proof (numVars_decodeAux_le x 0 []) as h. cbn [clauseBound] in h.
  unfold satSize, decode. lia.
Qed.

(** [iter f n x] applies [f] to [x] [n] times. *)
Fixpoint iter (f : Word -> Word) (n : nat) (x : Word) : Word :=
  match n with
  | 0 => x
  | S n' => iter f n' (f x)
  end.

(** A machine self-reduction with one call per level for the language [L],
    with size [satSize]: a machine [m] computes a step map [f] in polynomial
    time that never lengthens its input, lowers the size by one (down to 0)
    and keeps the answer of [L]; a machine [d] decides [L] in polynomial time
    on words of size 0.  This is the machine version of
    [AdditiveSelfReductionFor]. *)
Definition MachineSelfReductionOf (L : Language) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial) (d : Machine) (q : Polynomial),
    Computes m f p /\ (forall x, length (f x) <= length x) /\
    (forall x, satSize (f x) <= satSize x - 1 /\ L (f x) = L x) /\
    DecidesOn d q (fun y => satSize y = 0) L.

(** Open obligation.  SAT has a polynomial-time machine self-reduction with
    one recursive call per level ([MachineSelfReductionOf SAT]): a [Machine]
    ([Computes]) maps every encoded formula, in polynomial time and without
    lengthening it, to an equisatisfiable formula ([SAT (f x) = SAT x]) with
    one variable fewer, and a machine decides [SAT] on variable-free formulas
    ([DecidesOn]).  The familiar self-reduction ("set the next variable to
    both values") makes two calls per level and is exponential
    ([branchCost_exponential]). *)
Definition SATMachineSelfReduction : Prop := MachineSelfReductionOf SAT.

(** Known theorem, not mechanised here (closure of polynomial time under
    iteration of a length-non-increasing polynomial-time map a linear number
    of times).  If a machine computes [f] in polynomial time and
    [|f x| <= |x|], then some machine computes [x => iter f |x| x] in
    polynomial time: run [f] [|x|] times while keeping a counter, at cost at
    most [|x| * (p(|x|) + O(|x|))] on a multi-tape machine, and simulate that
    machine on one tape with quadratic overhead.  References: M. Sipser,
    Introduction to the Theory of Computation, 3rd ed., Theorem 7.8
    (multi-tape to single-tape simulation) and Section 7.2 (polynomial
    composition); S. Arora and B. Barak, Computational Complexity: A Modern
    Approach, Claim 1.6 and Section 1.6 (robustness of the model).  Used only
    as an explicit premise. *)
Definition IterationClosure : Prop :=
  forall (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p ->
    (forall x, length (f x) <= length x) ->
    exists (m' : Machine) (p' : Polynomial), Computes m' (fun x => iter f (length x) x) p'.

(** n steps lower the size by n and keep the answer. *)
Theorem iterate_spec : forall (L : Language) (f : Word -> Word),
  (forall x, satSize (f x) <= satSize x - 1 /\ L (f x) = L x) ->
  forall n x, satSize (iter f n x) <= satSize x - n /\ L (iter f n x) = L x.
Proof.
  intros L f hf n. induction n as [| n IH]; intro x; simpl; [split; [lia | reflexivity] |].
  destruct (IH (f x)) as [h1 h2]. destruct (hf x) as [h3 h4].
  split; [lia | rewrite h2, h4; reflexivity].
Qed.

(** Iterating the step [|x|] times reaches size 0 with the same answer. *)
Theorem iterate_length_spec : forall (L : Language) (f : Word -> Word),
  (forall x, satSize (f x) <= satSize x - 1 /\ L (f x) = L x) ->
  forall x, satSize (iter f (length x) x) = 0 /\ L x = L (iter f (length x) x).
Proof.
  intros L f hf x. destruct (iterate_spec L f hf (length x) x) as [h1 h2].
  pose proof (satSize_le_length x). split; [lia | symmetry; exact h2].
Qed.

(** Additive cost on machines.  Given the iteration closure, a machine
    self-reduction with one call per level puts [L] in P: iterate the step
    [|x|] times (a polynomial-time map into the size-0 promise, by
    [IterationClosure]) and compose with the base decider
    ([inP_of_promise_reduction]). *)
Theorem inP_of_machineSelfReduction : IterationClosure ->
  forall L : Language, MachineSelfReductionOf L -> InP L.
Proof.
  intros hI L [m [f [p [d [q [hm [hlen [hf hd]]]]]]]].
  destruct (hI m f p hm hlen) as [m' [p' hm']].
  exact (inP_of_promise_reduction L L (fun y => satSize y = 0) m' d
    (fun x => iter f (length x) x) p' q hm'
    (fun x => proj1 (iterate_length_spec L f hf x))
    (fun x => proj2 (iterate_length_spec L f hf x)) hd).
Qed.

(** Conditional theorem: the obligation puts SAT in P. *)
Theorem inP_sat_of_machineSelfReduction : IterationClosure ->
  SATMachineSelfReduction -> InP SAT.
Proof. intros hI h. exact (inP_of_machineSelfReduction hI SAT h). Qed.

(** Conditional theorem: with the Cook-Levin hardness of SAT ([SATHard], a
    known theorem used only as an explicit premise), the obligation gives
    P = NP. *)
Theorem pEqualsNP_of_machineSelfReduction : IterationClosure -> SATHard ->
  SATMachineSelfReduction -> PEqualsNP.
Proof.
  intros hI hard h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_machineSelfReduction hI h)).
Qed.

(* ---------- Non-vacuity: not every language has a machine self-reduction ---------- *)

(** A computable output reader.  Lean reads a machine's output with classical
    choice; Rocq follows at most [fuel] non-halting steps until the exit state
    [length (program m)] and reads [map ofBool w ++ blanks k] off the tape. *)
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

Definition readOutput (c : Config) : option Word :=
  match tapeLeft c with
  | [] => readBits (tapeHead c :: tapeRight c)
  | _ :: _ => None
  end.

(** The map computed by [m] within the clock [p] (the input itself where no
    output is read).  Lean's [mapOf m] is chosen classically. *)
Definition mapOf (mp : Machine * Polynomial) (x : Word) : Word :=
  match obind (exitWithin (fst mp) (initial x) (evalPoly (snd mp) (length x))) readOutput with
  | Some w => w
  | None => x
  end.

Theorem mapOf_eq : forall m f p, Computes m f p -> forall x, mapOf (m, p) x = f x.
Proof.
  intros m f p hm x. destruct (hm x) as [t [c [ht [hr [hcs [hcl [k hck]]]]]]].
  unfold mapOf. simpl fst. simpl snd.
  rewrite (exitWithin_of_reaches _ _ _ _ hr hcs _ ht). simpl.
  unfold readOutput. rewrite hcl, hck, readBits_bits. reflexivity.
Qed.

(** The answer of [d] on [y] within the clock [q] ([false] otherwise).
    Lean's [acceptsOf d] is classical and unclocked. *)
Definition acceptsOf (dq : Machine * Polynomial) (y : Word) : bool :=
  match runFor (fst dq) (initial y) (evalPoly (snd dq) (length y)) with
  | Some b => b
  | None => false
  end.

Theorem acceptsOf_eq : forall d q y t b, Run d (initial y) t b ->
  t <= evalPoly q (length y) -> acceptsOf (d, q) y = b.
Proof.
  intros d q y t b h ht. unfold acceptsOf. simpl fst. simpl snd.
  rewrite (runFor_of_run _ _ _ _ h _ ht). reflexivity.
Qed.

Theorem iter_ext : forall f g : Word -> Word, (forall x, f x = g x) ->
  forall n x, iter f n x = iter g n x.
Proof.
  intros f g hfg n. induction n as [| n IH]; intro x; simpl; [reflexivity |].
  rewrite hfg. apply IH.
Qed.

(** The language determined by a clocked step machine and a clocked base
    machine. *)
Definition selfReductionLanguage (md : (Machine * Polynomial) * (Machine * Polynomial))
    : Language :=
  fun x => acceptsOf (snd md) (iter (mapOf (fst md)) (length x) x).

Definition encPair (md : (Machine * Polynomial) * (Machine * Polynomial)) : Word :=
  encMachinePoly (fst md) ++ encMachinePoly (snd md).

(** Parse a machine/polynomial code from the front of a word. *)
Definition decMachinePolyFront (w : Word) : option ((Machine * Polynomial) * Word) :=
  obind (decMachineFront w) (fun '(m, r1) =>
  obind (decNat r1) (fun '(c, r2) =>
  obind (decNat r2) (fun '(k, r3) =>
  Some ((m, {| coefficient := c; degree := k |}), r3)))).

Theorem decMachinePolyFront_encMachinePoly : forall x r,
  decMachinePolyFront (encMachinePoly x ++ r) = Some (x, r).
Proof.
  intros [m [c k]] r. unfold decMachinePolyFront, encMachinePoly. simpl.
  rewrite <- !app_assoc, decMachineFront_encMachine. simpl.
  rewrite decNat_encNat. simpl. rewrite decNat_encNat. reflexivity.
Qed.

Definition decPair (w : Word) : option ((Machine * Polynomial) * (Machine * Polynomial)) :=
  obind (decMachinePolyFront w) (fun '(a, r) =>
  obind (decMachinePolyFront r) (fun '(b, _) => Some (a, b))).

Theorem decPair_encPair : forall md, decPair (encPair md) = Some md.
Proof.
  intros [a b]. unfold decPair, encPair. simpl.
  rewrite decMachinePolyFront_encMachinePoly. simpl.
  rewrite <- (app_nil_r (encMachinePoly b)), decMachinePolyFront_encMachinePoly.
  reflexivity.
Qed.

Theorem encPair_injective : forall a b, encPair a = encPair b -> a = b.
Proof. exact (injective_of_left_inverse encPair decPair decPair_encPair). Qed.

(** A language with a machine self-reduction agrees pointwise with the
    language of its pair of clocked machines (Lean states equality of
    functions). *)
Theorem machineSelfReductionOf_eq : forall L : Language, MachineSelfReductionOf L ->
  exists md, forall x, selfReductionLanguage md x = L x.
Proof.
  intros L [m [f [p [d [q [hm [_ [hf hd]]]]]]]].
  exists ((m, p), (d, q)). intro x.
  destruct (iterate_length_spec L f hf x) as [h0 hL].
  destruct (hd _ h0) as [t [b [ht [hrun hb]]]].
  unfold selfReductionLanguage. simpl fst. simpl snd.
  rewrite (iter_ext (mapOf (m, p)) f (mapOf_eq m f p hm)).
  rewrite (acceptsOf_eq _ _ _ _ _ hrun ht), hb, hL. reflexivity.
Qed.

(** The diagonal language against all pairs of clocked machines. *)
Definition selfReductionDiag : Language := fun w =>
  match decPair w with
  | Some md => negb (selfReductionLanguage md w)
  | None => true
  end.

(** Non-vacuity.  [MachineSelfReductionOf] is not a property of every
    language (diagonal argument over pairs of clocked machines), so the
    obligation [SATMachineSelfReduction] is a real constraint on SAT. *)
Theorem not_forall_machineSelfReductionOf : ~ (forall L : Language, MachineSelfReductionOf L).
Proof.
  intro hall.
  destruct (machineSelfReductionOf_eq selfReductionDiag (hall selfReductionDiag))
    as [md hmd].
  pose proof (hmd (encPair md)) as h.
  unfold selfReductionDiag in h. rewrite decPair_encPair in h.
  destruct (selfReductionLanguage md (encPair md)); discriminate h.
Qed.
