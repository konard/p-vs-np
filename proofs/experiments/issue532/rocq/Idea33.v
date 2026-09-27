(* Issue #532, Idea 33: average-case to worst-case transfer.

   Rocq counterpart of ../lean/Idea33.lean.  For every language L and every
   length n, the algorithm flipOne L (L with the answer flipped on the
   all-false input of each length) errs on exactly one of the 2^n inputs of
   length n, so its error fraction 1/2^n tends to 0, yet it is wrong in the
   worst case at every length.  The generic schema
   WorstToAverageObligationFor is therefore not automatic
   (obligation_not_automatic); its conditional use is obligation_transfers.

   Machine part (shared model, Machines.v): AvgPolyDec L delta (a clocked
   polynomial-time Machine wrong on at most delta n inputs of length n) and
   the transfer WorstToAverage L delta := AvgPolyDec L delta -> InP L; budget
   zero is exactly P (avgPolyDec_zero_iff); the transfer for SAT gives InP SAT
   and, with SATHard, P = NP (pEqualsNP_of_worstToAverage); refuting it gives
   P <> NP given SATInNP (pNotEqualsNP_of_not_worstToAverage); some language
   has no average-case decider with one error per length
   (exists_not_avgPolyDec).

   Verdict: refuted as an automatic inference.

   Differences from Lean:
   - Boolean tests A x != L x and A x == L x are negb (Bool.eqb (A x) (L x))
     and Bool.eqb (A x) (L x).
   - machineAnswer is computable (the step-bounded interpreter runFor with
     fuel p(|x|)) where Lean uses classical decide; machineAnswer_eq has the
     Lean statement.
   - exists_language_far_from_family takes a computable left inverse d of
     the code e (forall a, d (e a) = Some a) instead of injectivity of e, so
     that the far language is defined without classical logic. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(* Every bit string of length n. *)
Fixpoint allInputs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n => map (cons false) (allInputs n) ++ map (cons true) (allInputs n)
  end.

Definition count {A : Type} (p : A -> bool) (l : list A) : nat :=
  length (filter p l).

Lemma count_append {A : Type} (p : A -> bool) (l1 l2 : list A) :
  count p (l1 ++ l2) = count p l1 + count p l2.
Proof.
  unfold count. induction l1 as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; rewrite ?IH; reflexivity.
Qed.

Lemma count_map {A B : Type} (p : B -> bool) (f : A -> B) (l : list A) :
  count p (map f l) = count (fun a => p (f a)) l.
Proof.
  unfold count. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p (f a)); simpl; rewrite ?IH; reflexivity.
Qed.

Lemma count_false {A : Type} (l : list A) : count (fun _ => false) l = 0.
Proof. unfold count. induction l; simpl; auto. Qed.

Lemma count_le_length {A : Type} (p : A -> bool) (l : list A) :
  count p l <= length l.
Proof.
  unfold count. induction l as [|a l IH]; simpl; [lia|].
  destruct (p a); simpl; lia.
Qed.

Lemma count_add_count_not {A : Type} (p : A -> bool) (l : list A) :
  count p l + count (fun a => negb (p a)) l = length l.
Proof.
  unfold count. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; lia.
Qed.

Theorem allInputs_length : forall n, length (allInputs n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem length_of_mem_allInputs :
  forall n x, In x (allInputs n) -> length x = n.
Proof.
  induction n as [|n IH]; simpl; intros x H.
  - destruct H as [H|[]]. subst. reflexivity.
  - apply in_app_or in H. destruct H as [H|H];
      apply in_map_iff in H; destruct H as [y [Hy Hin]]; subst; simpl;
      rewrite (IH y Hin); reflexivity.
Qed.

Theorem mem_allInputs : forall x, In x (allInputs (length x)).
Proof.
  induction x as [|b x IH]; simpl; [left; reflexivity|].
  apply in_or_app. destruct b; [right|left]; apply in_map; exact IH.
Qed.

Lemma nodup_app_disjoint {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l IH]; simpl; intros H1 H2 Hdis; [exact H2|].
  inversion H1 as [|a' l' Hnot Hl]; subst.
  constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (Hnot Hin).
    + exact (Hdis a (or_introl eq_refl) Hin).
  - apply IH; [exact Hl | exact H2 | intros b Hb; apply Hdis; right; exact Hb].
Qed.

Lemma nodup_map_cons (b : bool) (l : list (list bool)) :
  NoDup l -> NoDup (map (cons b) l).
Proof.
  induction l as [|a l IH]; simpl; intro H; [apply NoDup_nil|].
  inversion H as [|a' l' Hnot Hl]; subst.
  apply NoDup_cons; [|apply IH; exact Hl].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hy']].
  inversion Hy; subst. exact (Hnot Hy').
Qed.

Theorem allInputs_nodup : forall n, NoDup (allInputs n).
Proof.
  induction n as [|n IH]; simpl.
  - apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
  - apply nodup_app_disjoint.
    + apply nodup_map_cons. exact IH.
    + apply nodup_map_cons. exact IH.
    + intros a Ha Hb. apply in_map_iff in Ha. apply in_map_iff in Hb.
      destruct Ha as [y [Hy _]]. destruct Hb as [z [Hz _]]. subst. discriminate.
Qed.

Definition zeros (n : nat) : list bool := repeat false n.

Fixpoint isZeros (x : list bool) : bool :=
  match x with
  | [] => true
  | b :: x => negb b && isZeros x
  end.

Lemma isZeros_zeros : forall n, isZeros (zeros n) = true.
Proof. induction n; simpl; auto. Qed.

Definition flipOne (L : list bool -> bool) (x : list bool) : bool :=
  if isZeros x then negb (L x) else L x.

Theorem count_isZeros : forall n, count isZeros (allInputs n) = 1.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite count_append, !count_map. simpl.
  replace (count (fun a : list bool => false) (allInputs n)) with 0
    by (symmetry; apply count_false).
  rewrite Nat.add_0_r. exact IH.
Qed.

Lemma flipOne_disagree_iff (L : list bool -> bool) (x : list bool) :
  negb (Bool.eqb (flipOne L x) (L x)) = isZeros x.
Proof. unfold flipOne. destruct (isZeros x), (L x); reflexivity. Qed.

Lemma count_ext {A : Type} (p q : A -> bool) (l : list A) :
  (forall a, p a = q a) -> count p l = count q l.
Proof.
  intro H. unfold count. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H. destruct (q a); simpl; rewrite ?IH; reflexivity.
Qed.

(* Average case: exactly one error among the 2^n inputs of length n. *)
Theorem flipOne_errors (L : list bool -> bool) (n : nat) :
  count (fun x => negb (Bool.eqb (flipOne L x) (L x))) (allInputs n) = 1.
Proof.
  rewrite (count_ext _ isZeros); [apply count_isZeros|].
  intro a. apply flipOne_disagree_iff.
Qed.

(* Average case: correct on exactly 2^n - 1 inputs of length n. *)
Theorem flipOne_agreements (L : list bool -> bool) (n : nat) :
  count (fun x => Bool.eqb (flipOne L x) (L x)) (allInputs n) = 2 ^ n - 1.
Proof.
  pose proof (count_add_count_not (fun x => Bool.eqb (flipOne L x) (L x)) (allInputs n)) as H.
  cbv beta in H. rewrite flipOne_errors, allInputs_length in H. lia.
Qed.

Lemma lt_two_pow_self : forall n, n < 2 ^ n.
Proof. induction n; simpl; lia. Qed.

Lemma two_pow_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. apply Nat.pow_le_mono_r; lia. Qed.

(* Vanishing error: from length k on, the error fraction is at most 1/k. *)
Theorem flipOne_error_vanishes (L : list bool -> bool) (k : nat) :
  forall n, k <= n ->
    count (fun x => negb (Bool.eqb (flipOne L x) (L x))) (allInputs n) * k <= 2 ^ n.
Proof.
  intros n Hn. rewrite flipOne_errors, Nat.mul_1_l.
  pose proof (lt_two_pow_self k). pose proof (two_pow_mono k n Hn). lia.
Qed.

Lemma flipOne_zeros (L : list bool -> bool) (n : nat) :
  flipOne L (zeros n) <> L (zeros n).
Proof.
  unfold flipOne. rewrite isZeros_zeros. destruct (L (zeros n)); discriminate.
Qed.

Lemma flipOne_zeros_ne (L : list bool -> bool) (n : nat) :
  exists x, flipOne L x <> L x.
Proof. exists (zeros n). apply flipOne_zeros. Qed.

(* Worst case: wrong on some input of every length. *)
Theorem flipOne_worst_case_wrong (L : list bool -> bool) (n : nat) :
  exists x, length x = n /\ flipOne L x <> L x.
Proof.
  exists (zeros n). split; [apply repeat_length|apply flipOne_zeros].
Qed.

(* Main refutation. *)
Theorem average_case_does_not_imply_worst_case (L : list bool -> bool) :
  exists A : list bool -> bool,
    (forall n, count (fun x => Bool.eqb (A x) (L x)) (allInputs n) = 2 ^ n - 1) /\
    (forall n, count (fun x => negb (Bool.eqb (A x) (L x))) (allInputs n) = 1) /\
    (forall n, exists x, length x = n /\ A x <> L x).
Proof.
  exists (flipOne L). split; [|split].
  - apply flipOne_agreements.
  - apply flipOne_errors.
  - apply flipOne_worst_case_wrong.
Qed.

Definition AvgCorrect (A L : list bool -> bool) (delta : nat -> nat) : Prop :=
  forall n, count (fun x => negb (Bool.eqb (A x) (L x))) (allInputs n) <= delta n.

Definition WorstCorrect (A L : list bool -> bool) : Prop := forall x, A x = L x.

Theorem worst_implies_avg (A L : list bool -> bool) (delta : nat -> nat) :
  WorstCorrect A L -> AvgCorrect A L delta.
Proof.
  intros H n. rewrite (count_ext _ (fun _ => false)).
  - rewrite count_false. lia.
  - intro a. rewrite H. destruct (L a); reflexivity.
Qed.

Theorem avg_zero_implies_worst (A L : list bool -> bool) :
  AvgCorrect A L (fun _ => 0) -> WorstCorrect A L.
Proof.
  intros H x. pose proof (H (length x)) as H0. simpl in H0.
  destruct (Bool.eqb (A x) (L x)) eqn:E.
  - apply Bool.eqb_prop. exact E.
  - exfalso.
    assert (Hin : In x (filter (fun y => negb (Bool.eqb (A y) (L y))) (allInputs (length x)))).
    { apply filter_In. split; [apply mem_allInputs|rewrite E; reflexivity]. }
    unfold count in H0.
    destruct (filter (fun y => negb (Bool.eqb (A y) (L y))) (allInputs (length x))).
    + destruct Hin.
    + simpl in H0. lia.
Qed.

(** Generic schema over a free algorithm class Efficient, a language L and an
    error budget delta: an efficient average-case solver yields an efficient
    worst-case solver.  Its truth depends on the choice of Efficient
    (obligation_not_automatic); the machine instance is WorstToAverage below,
    with Efficient replaced by Run step counts. *)
Definition WorstToAverageObligationFor (Efficient : (list bool -> bool) -> Prop)
    (L : list bool -> bool) (delta : nat -> nat) : Prop :=
  (exists A, Efficient A /\ AvgCorrect A L delta) ->
  exists B, Efficient B /\ WorstCorrect B L.

Theorem obligation_not_automatic (L : list bool -> bool) :
  exists Efficient : (list bool -> bool) -> Prop,
    ~ WorstToAverageObligationFor Efficient L (fun _ => 1).
Proof.
  exists (fun A => exists x, A x <> L x). intro Hob.
  destruct Hob as [B [[x Hx] HB]].
  - exists (flipOne L). split; [apply (flipOne_zeros_ne L 0)|].
    intro n. rewrite flipOne_errors. lia.
  - exact (Hx (HB x)).
Qed.

Theorem obligation_transfers (Efficient : (list bool -> bool) -> Prop)
    (L : list bool -> bool) (delta : nat -> nat) :
  WorstToAverageObligationFor Efficient L delta ->
  forall A, Efficient A -> AvgCorrect A L delta ->
  exists B, Efficient B /\ WorstCorrect B L.
Proof. intros Hob A HA Havg. apply Hob. exists A. auto. Qed.

Example size_three_check :
  count (fun x => Bool.eqb (flipOne (fun _ => true) x) true) (allInputs 3) = 7.
Proof. reflexivity. Qed.

(* ---------- Machine part: average-case deciders in the shared model ---------- *)

(** The answer of m within the clock p: accept iff it accepts within p(|x|)
    steps (computable, by the step-bounded interpreter runFor). *)
Definition machineAnswer (m : Machine) (p : Polynomial) : Language := fun x =>
  match runFor m (initial x) (evalPoly p (length x)) with
  | Some true => true
  | _ => false
  end.

Theorem machineAnswer_eq : forall m p x t b,
  t <= evalPoly p (length x) -> Run m (initial x) t b -> machineAnswer m p x = b.
Proof.
  intros m p x t b ht hr. unfold machineAnswer.
  rewrite (runFor_of_run _ _ _ _ hr _ ht). destruct b; reflexivity.
Qed.

(** L has a polynomial-time machine that halts on every input within the
    clock and errs on at most delta n inputs of each length n. *)
Definition AvgPolyDec (L : Language) (delta : nat -> nat) : Prop :=
  exists (m : Machine) (p : Polynomial),
    (forall x, exists t b, t <= evalPoly p (length x) /\ Run m (initial x) t b) /\
    AvgCorrect (machineAnswer m p) L delta.

(** Machine instance of the schema: an average-case polynomial-time machine
    decider for L with error budget delta gives a worst-case one.  The
    distribution is uniform on words; for SAT most words decode to a CNF that
    contains the empty clause, so this is not the samplable-distribution
    statement of the literature (see the dossier). *)
Definition WorstToAverage (L : Language) (delta : nat -> nat) : Prop :=
  AvgPolyDec L delta -> InP L.

(** A worst-case decider is an average-case decider for every budget. *)
Theorem avgPolyDec_of_inP : forall L, InP L -> forall delta, AvgPolyDec L delta.
Proof.
  intros L h delta. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  exists m, p. split.
  - intro x. destruct (hm x) as [t [b [ht [hr _]]]]. exists t, b. auto.
  - apply worst_implies_avg. intro x. destruct (hm x) as [t [b [ht [hr hb]]]].
    rewrite (machineAnswer_eq _ _ _ _ _ ht hr). exact hb.
Qed.

(** With budget zero an average-case decider is a worst-case decider. *)
Theorem inP_of_avgPolyDec_zero : forall L, AvgPolyDec L (fun _ => 0) -> InP L.
Proof.
  intros L [m [p [hhalt havg]]].
  pose proof (avg_zero_implies_worst _ _ havg) as hw.
  apply (inP_of_decidesWithin m p). intro x.
  destruct (hhalt x) as [t [b [ht hr]]]. exists t, b.
  split; [exact ht | split; [exact hr |]].
  rewrite <- hw. symmetry. exact (machineAnswer_eq _ _ _ _ _ ht hr).
Qed.

Theorem avgPolyDec_zero_iff : forall L, AvgPolyDec L (fun _ => 0) <-> InP L.
Proof.
  intro L. split; [apply inP_of_avgPolyDec_zero | intro h; exact (avgPolyDec_of_inP L h _)].
Qed.

Theorem worstToAverage_of_inP : forall L, InP L -> forall delta, WorstToAverage L delta.
Proof. intros L h delta _. exact h. Qed.

Theorem worstToAverage_zero : forall L, WorstToAverage L (fun _ => 0).
Proof. intro L. exact (inP_of_avgPolyDec_zero L). Qed.

(** Conditional theorem (proved).  The transfer for SAT plus an average-case
    machine decider for SAT gives InP SAT. *)
Theorem inP_sat_of_worstToAverage : forall delta,
  WorstToAverage SAT delta -> AvgPolyDec SAT delta -> InP SAT.
Proof. intros delta h havg. exact (h havg). Qed.

(** Conditional theorem (proved).  With SAT's NP-hardness (a named
    hypothesis) the same data give P = NP. *)
Theorem pEqualsNP_of_worstToAverage : SATHard -> forall delta,
  WorstToAverage SAT delta -> AvgPolyDec SAT delta -> PEqualsNP.
Proof. intros hard delta h havg. exact (pEqualsNP_of_inP_sat hard (h havg)). Qed.

(** Under P = NP (and SAT in NP) the transfer for SAT holds for every
    budget. *)
Theorem worstToAverage_sat_of_pEqualsNP : SATInNP -> PEqualsNP ->
  forall delta, WorstToAverage SAT delta.
Proof.
  intros mem hp delta. exact (worstToAverage_of_inP _ (inP_sat_of_pEqualsNP mem hp) delta).
Qed.

(** Conditional theorem (proved).  Refuting the transfer for SAT at any
    budget proves P <> NP (given SAT in NP). *)
Theorem pNotEqualsNP_of_not_worstToAverage : SATInNP -> forall delta,
  ~ WorstToAverage SAT delta -> PNotEqualsNP.
Proof. intros mem delta h hp. exact (h (worstToAverage_sat_of_pEqualsNP mem hp delta)). Qed.

(* ---------- Non-vacuity: a language far from every machine ---------- *)

Theorem two_le_count : forall {A : Type} (q : A -> bool) (l : list A) (x y : A),
  x <> y -> In x l -> In y l -> q x = true -> q y = true -> 2 <= count q l.
Proof.
  intros A q l x y hxy hx hy hqx hqy. unfold count.
  change 2 with (length [x; y]). apply NoDup_incl_length.
  - constructor; [simpl; intros [h | []]; exact (hxy (eq_sym h)) |].
    constructor; [intros [] | constructor].
  - intros z [<- | [<- | []]]; apply filter_In; auto.
Qed.

(** Two-point Cantor argument.  For a family of languages indexed by a type
    whose code e has a computable left inverse d, there is a language that
    differs from the a-th member on both one-bit extensions of the code of
    a. *)
Theorem exists_language_far_from_family : forall {T : Type} (e : T -> Word)
    (d : Word -> option T), (forall a, d (e a) = Some a) ->
  forall F : T -> Language,
    exists L : Language, forall a (b : bool), F a (e a ++ [b]) <> L (e a ++ [b]).
Proof.
  intros T e d hd F.
  exists (fun w => match d (removelast w) with
                   | Some a => negb (F a w)
                   | None => true
                   end).
  intros a b hFa. cbv beta in hFa. rewrite removelast_last, hd in hFa.
  destruct (F a (e a ++ [b])); discriminate.
Qed.

(** Non-vacuity.  Some language has no average-case polynomial-time machine
    decider even with one error per length allowed. *)
Theorem exists_not_avgPolyDec : exists L : Language, ~ AvgPolyDec L (fun _ => 1).
Proof.
  destruct (exists_language_far_from_family encMachinePoly decMachinePoly
              decMachinePoly_encMachinePoly (fun a => machineAnswer (fst a) (snd a)))
    as [L hL].
  exists L. intros [m [p [_ havg]]].
  set (w := encMachinePoly (m, p)).
  assert (hmem : forall b : bool, In (w ++ [b]) (allInputs (length w + 1))).
  { intro b. pose proof (mem_allInputs (w ++ [b])) as h.
    rewrite length_app in h. exact h. }
  assert (herr : forall b : bool,
    negb (Bool.eqb (machineAnswer m p (w ++ [b])) (L (w ++ [b]))) = true).
  { intro b. pose proof (hL (m, p) b) as h. simpl in h. fold w in h.
    destruct (machineAnswer m p (w ++ [b])), (L (w ++ [b])); try reflexivity;
      exfalso; exact (h eq_refl). }
  assert (hne : w ++ [false] <> w ++ [true]).
  { intro h. apply app_inv_head in h. discriminate. }
  pose proof (two_le_count (fun x => negb (Bool.eqb (machineAnswer m p x) (L x)))
    _ _ _ hne (hmem false) (hmem true) (herr false) (herr true)) as h2.
  pose proof (havg (length w + 1)) as h1.
  pose proof (Nat.le_trans _ _ _ h2 h1). lia.
Qed.

(** Non-vacuity of the transfer: it holds at budget zero for every language;
    exists_not_avgPolyDec shows that its hypothesis is not automatic at
    budget one. *)
Theorem worstToAverage_nontrivial :
  (forall L, WorstToAverage L (fun _ => 0)) /\
  exists L : Language, ~ AvgPolyDec L (fun _ => 1).
Proof. split; [exact worstToAverage_zero | exact exists_not_avgPolyDec]. Qed.
