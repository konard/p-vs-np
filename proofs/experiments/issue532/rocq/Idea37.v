(* Issue #532, Idea 37: parameterized structure.

   Rocq counterpart of ../lean/Idea37.lean (same theorem names and content).
   An FPT bound f(k) * n^c is polynomial when f(k) <= n^a, in particular when
   2^k <= n (logarithmic parameter). When the parameter equals the input size,
   2^n * n^c exceeds every polynomial a * (n+1)^d somewhere.

   LogParamFPTObligationFor is a generic schema (Correct and time are
   parameters): a correct algorithm with a 2^k * n^c bound for a parameter
   that is logarithmic on all instances has a polynomial bound
   (obligation_gives_poly_time).

   Over the shared machine model (Complexity.Machine, time = step count of
   Complexity.Run): LogParamFPT L says a machine decides L within
   2^(param x) * (|x|+1)^c steps with 2^(param x) <= (|x|+1)^b on every word;
   logParamFPT_inP puts L in P.  The open obligation is
   LogParamFPTObligation := LogParamFPT SAT; logParam_route_gives_pEqualsNP
   turns it into PEqualsNP given SATHard (the hard half of Cook-Levin, a
   named premise, not proved).  not_forall_logParamFPT shows LogParamFPT is
   not provable for every language.  logParamFPT_iff_schema shows the machine
   statement is the schema instantiated with machines and their step counts.

   Difference from Lean: Lean's steps m x is defined for every machine with
   Classical.choose (and is 0 on non-halting inputs).  Here the algorithms of
   the schema are HaltingMachine values (a machine together with a proof that
   it halts on every word), and steps finds the length of the unique halting
   run by a constructive search (ConstructiveEpsilon), using the exact-length
   interpreter runExact.  steps_eq and logParamFPT_iff_schema have the Lean
   statements with Machine replaced by HaltingMachine.  No axioms are used. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
From Stdlib Require Import ConstructiveEpsilon.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(* The FPT bound and the schema. *)

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

(** Generic schema (not tied to a machine model): a correct algorithm with a
    [2^k * n^c] FPT bound for a parameter that is logarithmic on all
    instances.  [Correct] and [time] are parameters; [logParamFPT_iff_schema]
    shows that the machine statement [LogParamFPT] is this schema
    instantiated with machines and their step counts. *)
Definition LogParamFPTObligationFor {Inst Alg : Type} (Correct : Alg -> Prop)
    (time : Alg -> Inst -> nat) (size : Inst -> nat) : Prop :=
  exists (A : Alg) (param : Inst -> nat) (c b : nat),
    Correct A /\ FPTBound (time A) size param (fun k => 2 ^ k) c /\ LogBoundedParam size param b.

Theorem obligation_gives_poly_time {Inst Alg : Type} (Correct : Alg -> Prop)
    (time : Alg -> Inst -> nat) (size : Inst -> nat) :
  LogParamFPTObligationFor Correct time size ->
  exists A d, Correct A /\ forall I, time A I <= size I ^ d.
Proof.
  intros [A [param [c [b [HA [Hfpt Hlog]]]]]].
  exists A, (b + c). split; [exact HA|].
  apply (fpt_log_param_polytime (time A) size param c b Hfpt Hlog).
Qed.

Example numeric_check : 2 ^ 4 * 16 ^ 2 <= 16 ^ 3.
Proof. apply Nat.leb_le. reflexivity. Qed.

(* The obligation over the shared machine model.

   A decider is a Complexity.Machine; its running time on x is the step count
   t of the run Run m (initial x) t b; the size of x is |x| + 1 (as in
   evalPoly). *)

(** A machine decides [L] within [2^(param x) * (|x|+1)^c] steps, for a
    parameter [param] with [2^(param x) <= (|x|+1)^b] on every word [x]. *)
Definition LogParamFPT (L : Language) : Prop :=
  exists (m : Machine) (param : Word -> nat) (c b : nat),
    (forall x, 2 ^ param x <= (length x + 1) ^ b) /\
    forall x, exists t v, t <= 2 ^ param x * (length x + 1) ^ c /\
      Run m (initial x) t v /\ v = L x.

(* FPT with a logarithmic parameter is in P (machine model): the step bound is
   at most the polynomial (|x|+1)^(b+c). *)
Theorem logParamFPT_inP : forall L : Language, LogParamFPT L -> InP L.
Proof.
  intros L [m [param [c [b [hlog hrun]]]]].
  apply (inP_of_decidesWithin m {| coefficient := 1; degree := b + c |}).
  intro x. destruct (hrun x) as [t [v [ht [hr hv]]]].
  exists t, v. split; [| split; [exact hr | exact hv]].
  unfold evalPoly. simpl coefficient. simpl degree.
  rewrite Nat.mul_1_l, Nat.pow_add_r.
  eapply Nat.le_trans; [exact ht |]. apply Nat.mul_le_mono_r. apply hlog.
Qed.

(** Open obligation.  SAT (the shared encoding [Machines.SAT]) is decided by
    a machine within [2^(param x) * (|x|+1)^c] steps for a parameter with
    [2^(param x) <= (|x|+1)^b] on every word. *)
Definition LogParamFPTObligation : Prop := LogParamFPT SAT.

(* Conditional theorem.  The obligation puts SAT in P. *)
Theorem logParam_obligation_inP : LogParamFPTObligation -> InP SAT.
Proof. exact (logParamFPT_inP SAT). Qed.

(* Conditional theorem.  With NP-hardness of SAT (SATHard, the hard half of
   Cook-Levin, a named premise) the obligation gives P = NP. *)
Theorem logParam_route_gives_pEqualsNP : SATHard -> LogParamFPTObligation -> PEqualsNP.
Proof. intros hard h. exact (pEqualsNP_of_inP_sat hard (logParamFPT_inP SAT h)). Qed.

(* Non-vacuity.  LogParamFPT is not provable for every language. *)
Theorem not_forall_logParamFPT : ~ (forall L : Language, LogParamFPT L).
Proof.
  intro hall. destruct exists_not_inP as [L hL].
  exact (hL (logParamFPT_inP L (hall L))).
Qed.

(* The machine statement is the schema instantiated with machines. *)

(** Run [m] from [c] for exactly [t] steps: [Some b] iff [Run m c t b]. *)
Fixpoint runExact (m : Machine) (c : Config) (t : nat) : option bool :=
  match t with
  | 0 => None
  | S t' =>
      match step m c with
      | inl b => match t' with 0 => Some b | S _ => None end
      | inr c' => runExact m c' t'
      end
  end.

Lemma run_of_runExact : forall m t c b, runExact m c t = Some b -> Run m c t b.
Proof.
  intros m t. induction t as [| t IH]; intros c b h; simpl in h; [discriminate |].
  destruct (step m c) as [b' | c'] eqn:hs.
  - destruct t; [| discriminate]. injection h as <-. apply run_halt. exact hs.
  - apply run_next with c'; [exact hs | apply IH; exact h].
Qed.

Lemma runExact_of_run : forall m c t b, Run m c t b -> runExact m c t = Some b.
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs _ IH]; simpl; rewrite hs;
    [reflexivity | exact IH].
Qed.

(** Whether [m] halts from [c] after exactly [t] steps is decidable. *)
Definition run_dec (m : Machine) (c : Config) (t : nat) :
    {exists v, Run m c t v} + {~ exists v, Run m c t v}.
Proof.
  destruct (runExact m c t) as [v |] eqn:E.
  - left. exists v. apply run_of_runExact. exact E.
  - right. intros [v hv]. rewrite (runExact_of_run m c t v hv) in E. discriminate.
Defined.

(** A machine together with a proof that it halts on every word. *)
Record HaltingMachine := {
  hmMachine : Machine;
  hmHalts : forall x, exists t v, Run hmMachine (initial x) t v
}.

(** The step count of a halting machine on [x]: the length of its (unique)
    halting run from [initial x], found by a constructive search. *)
Definition steps (A : HaltingMachine) (x : Word) : nat :=
  proj1_sig (constructive_indefinite_ground_description_nat
    (fun t => exists v, Run (hmMachine A) (initial x) t v)
    (run_dec (hmMachine A) (initial x)) (hmHalts A x)).

Lemma steps_spec : forall A x, exists v, Run (hmMachine A) (initial x) (steps A x) v.
Proof.
  intros A x. unfold steps.
  exact (proj2_sig (constructive_indefinite_ground_description_nat
    (fun t => exists v, Run (hmMachine A) (initial x) t v)
    (run_dec (hmMachine A) (initial x)) (hmHalts A x))).
Qed.

(* The step count steps A x is the length of any halting run on x. *)
Theorem steps_eq : forall (A : HaltingMachine) (x : Word) (t : nat) (v : bool),
  Run (hmMachine A) (initial x) t v -> steps A x = t.
Proof.
  intros A x t v hr. destruct (steps_spec A x) as [v' hv'].
  exact (proj1 (run_deterministic _ _ _ _ _ _ hv' hr)).
Qed.

(** A halting machine answers [L x] on every word. *)
Definition MachineDecides (L : Language) (A : HaltingMachine) : Prop :=
  forall x, Run (hmMachine A) (initial x) (steps A x) (L x).

(* Instantiation.  LogParamFPT L is exactly the schema LogParamFPTObligationFor
   with algorithms = halting machines, Correct = "decides L", time = the
   machine step count steps, and size |x| + 1. *)
Theorem logParamFPT_iff_schema : forall L : Language,
  LogParamFPT L <->
    @LogParamFPTObligationFor Word HaltingMachine (MachineDecides L) steps
      (fun x => length x + 1).
Proof.
  intro L. split.
  - intros [m [param [c [b [hlog hrun]]]]].
    assert (hh : forall x, exists t v, Run m (initial x) t v).
    { intro x. destruct (hrun x) as [t [v [_ [hr _]]]]. exists t, v. exact hr. }
    exists (Build_HaltingMachine m hh), param, c, b.
    split; [| split; [| exact hlog]].
    + intro x. destruct (hrun x) as [t [v [_ [hr hv]]]].
      rewrite (steps_eq (Build_HaltingMachine m hh) x t v hr), <- hv. exact hr.
    + intro x. destruct (hrun x) as [t [v [ht [hr _]]]].
      rewrite (steps_eq (Build_HaltingMachine m hh) x t v hr). exact ht.
  - intros [A [param [c [b [hdec [hfpt hlog]]]]]].
    exists (hmMachine A), param, c, b. split; [exact hlog |].
    intro x. exists (steps A x), (L x). split; [exact (hfpt x) |].
    split; [exact (hdec x) | reflexivity].
Qed.
