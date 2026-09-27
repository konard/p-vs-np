(* Issue #532, Idea 15: circuit depth versus size.

   Rocq counterpart of lean/Idea15.lean; theorem names are aligned.

   Formulas over variables, NOT and fan-in-2 AND/OR.  Proved in general:
   depth f < size f < 2^(depth f + 1) and leaves f <= 2^(depth f); the AND
   chain attains depth = size - 1 / 2, the balanced AND tree attains
   size = 2^(depth+1) - 1; for every d both compute the AND of 2^d variables
   with the same size and depths 2^d - 1 versus d; and a superpolynomial
   formula-size lower bound implies a superlogarithmic depth lower bound.

   Tie to the shared machine model.  FormulaSizeLBFor and DepthLBFor are
   schemas over a formula family.  Their instances for the language SAT of
   Machines.v, read at length n through [slice SAT n] of Circuits.v, are the
   open obligations SATFormulaSizeLB and SATDepthLB.  With SATInNP,
   SATDepthLB gives NPNotInLogDepth (an NC1-type separation), the honest
   conclusion.  P <> NP additionally needs PSubsetLogDepth (P in NC1, open
   and not assumed anywhere), see pNotEqualsNP_of_satDepthLB.  Non-vacuity:
   andPow_sizeLB, andPow_depthLB (a family reading 2 ^ n variables meets
   both shapes), var0_not_depthLB and var0_not_sizeLB (a one-leaf family
   meets neither).

   Verdict: size and depth are distinct resources; even the open obligation
   SATDepthLB would give NP not in NC^1, not P <> NP.
   Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.

Inductive F : Type :=
  | Var : nat -> F
  | Neg : F -> F
  | Conj : F -> F -> F
  | Disj : F -> F -> F.

Fixpoint eval (rho : nat -> bool) (f : F) : bool :=
  match f with
  | Var i => rho i
  | Neg g => negb (eval rho g)
  | Conj g h => eval rho g && eval rho h
  | Disj g h => eval rho g || eval rho h
  end.

Fixpoint size (f : F) : nat :=
  match f with
  | Var _ => 1
  | Neg g => size g + 1
  | Conj g h => size g + size h + 1
  | Disj g h => size g + size h + 1
  end.

Fixpoint leaves (f : F) : nat :=
  match f with
  | Var _ => 1
  | Neg g => leaves g
  | Conj g h => leaves g + leaves h
  | Disj g h => leaves g + leaves h
  end.

Fixpoint depth (f : F) : nat :=
  match f with
  | Var _ => 0
  | Neg g => depth g + 1
  | Conj g h => Nat.max (depth g) (depth h) + 1
  | Disj g h => Nat.max (depth g) (depth h) + 1
  end.

Lemma two_pow_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b h. apply Nat.pow_le_mono_r; lia. Qed.

Lemma pow2_succ : forall n, 2 ^ (n + 1) = 2 * 2 ^ n.
Proof. intro n. rewrite Nat.add_1_r. reflexivity. Qed.

(** A formula of depth d has fewer than 2^(d+1) nodes. *)
Theorem size_le_pow_depth : forall f, size f + 1 <= 2 ^ (depth f + 1).
Proof.
  induction f as [i | g IH | g IHg h IHh | g IHg h IHh]; simpl.
  - lia.
  - rewrite (pow2_succ (depth g + 1)). lia.
  - pose proof (two_pow_mono (depth g + 1) (Nat.max (depth g) (depth h) + 1) ltac:(lia)).
    pose proof (two_pow_mono (depth h + 1) (Nat.max (depth g) (depth h) + 1) ltac:(lia)).
    rewrite (pow2_succ (Nat.max (depth g) (depth h) + 1)). lia.
  - pose proof (two_pow_mono (depth g + 1) (Nat.max (depth g) (depth h) + 1) ltac:(lia)).
    pose proof (two_pow_mono (depth h + 1) (Nat.max (depth g) (depth h) + 1) ltac:(lia)).
    rewrite (pow2_succ (Nat.max (depth g) (depth h) + 1)). lia.
Qed.

(** A formula of depth d has at most 2^d leaves. *)
Theorem leaves_le_pow_depth : forall f, leaves f <= 2 ^ depth f.
Proof.
  induction f as [i | g IH | g IHg h IHh | g IHg h IHh]; simpl.
  - lia.
  - pose proof (two_pow_mono (depth g) (depth g + 1) ltac:(lia)). lia.
  - pose proof (two_pow_mono (depth g) (Nat.max (depth g) (depth h)) ltac:(lia)).
    pose proof (two_pow_mono (depth h) (Nat.max (depth g) (depth h)) ltac:(lia)).
    rewrite Nat.add_1_r, Nat.pow_succ_r'. lia.
  - pose proof (two_pow_mono (depth g) (Nat.max (depth g) (depth h)) ltac:(lia)).
    pose proof (two_pow_mono (depth h) (Nat.max (depth g) (depth h)) ltac:(lia)).
    rewrite Nat.add_1_r, Nat.pow_succ_r'. lia.
Qed.

(** Depth is less than size. *)
Theorem depth_lt_size : forall f, depth f < size f.
Proof. induction f; simpl; lia. Qed.

(** Left-deep AND chain. *)
Fixpoint chain (n : nat) : F :=
  match n with 0 => Var 0 | S m => Conj (chain m) (Var (S m)) end.

(** Balanced AND tree on 2^d variables starting at i * 2^d. *)
Fixpoint bal (d i : nat) : F :=
  match d with 0 => Var i | S e => Conj (bal e (2 * i)) (bal e (2 * i + 1)) end.

Fixpoint andRange (a m : nat) (rho : nat -> bool) : bool :=
  match m with 0 => true | S k => andRange a k rho && rho (a + k) end.

Lemma andRange_add : forall a m n rho,
  andRange a (m + n) rho = andRange a m rho && andRange (a + m) n rho.
Proof.
  intros a m n rho. induction n; simpl.
  - rewrite Nat.add_0_r, andb_true_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IHn, <- andb_assoc, Nat.add_assoc. reflexivity.
Qed.

Theorem chain_size : forall n, size (chain n) = 2 * n + 1.
Proof. induction n; simpl in *; lia. Qed.

Theorem chain_depth : forall n, depth (chain n) = n.
Proof. induction n; simpl in *; lia. Qed.

Theorem eval_chain : forall n rho, eval rho (chain n) = andRange 0 (n + 1) rho.
Proof.
  intros n rho. induction n; simpl; [reflexivity|].
  rewrite IHn. rewrite Nat.add_1_r. reflexivity.
Qed.

Theorem bal_size : forall d i, size (bal d i) + 1 = 2 ^ (d + 1).
Proof.
  induction d; intro i; [reflexivity|].
  cbn [bal size]. pose proof (IHd (2 * i)). pose proof (IHd (2 * i + 1)).
  replace (S d + 1) with ((d + 1) + 1) by lia. rewrite (pow2_succ (d + 1)). lia.
Qed.

Theorem bal_depth : forall d i, depth (bal d i) = d.
Proof. induction d; intro i; simpl; [reflexivity|]. rewrite !IHd. lia. Qed.

Theorem eval_bal : forall d i rho, eval rho (bal d i) = andRange (i * 2 ^ d) (2 ^ d) rho.
Proof.
  induction d; intros i rho.
  - simpl. rewrite Nat.mul_1_r, Nat.add_0_r. reflexivity.
  - cbn [bal eval]. rewrite !IHd.
    replace (i * 2 ^ S d) with (2 * i * 2 ^ d) by (rewrite Nat.pow_succ_r'; ring).
    replace (2 ^ S d) with (2 ^ d + 2 ^ d) by (rewrite Nat.pow_succ_r'; ring).
    rewrite andRange_add.
    replace ((2 * i + 1) * 2 ^ d) with (2 * i * 2 ^ d + 2 ^ d) by ring.
    reflexivity.
Qed.

(** Same function, same size, exponentially different depth. *)
Theorem same_function_different_depth : forall d,
  (forall rho, eval rho (chain (2 ^ d - 1)) = eval rho (bal d 0)) /\
  size (chain (2 ^ d - 1)) = size (bal d 0) /\
  depth (chain (2 ^ d - 1)) = 2 ^ d - 1 /\ depth (bal d 0) = d.
Proof.
  intro d. pose proof (two_pow_mono 0 d ltac:(lia)) as hpos. simpl in hpos.
  split; [|split; [|split]].
  - intro rho. rewrite eval_chain, eval_bal, Nat.mul_0_l.
    replace (2 ^ d - 1 + 1) with (2 ^ d) by lia. reflexivity.
  - pose proof (bal_size d 0) as h. rewrite chain_size.
    rewrite pow2_succ in h. lia.
  - apply chain_depth.
  - apply bal_depth.
Qed.

(** [f] computes the Boolean function [g]. *)
Definition FormulaComputes (f : F) (g : (nat -> bool) -> bool) : Prop :=
  forall rho, eval rho f = g rho.

(** Schema: the family [fam] has superpolynomial formula size: for every c
    there is an n where every formula for [fam n] has size at least
    2^(c * (log2 n + 1)) (roughly n^c).  The family is a parameter; the SAT
    instance is [SATFormulaSizeLB]. *)
Definition FormulaSizeLBFor (fam : nat -> (nat -> bool) -> bool) : Prop :=
  forall c, exists n, forall f, FormulaComputes f (fam n) ->
    2 ^ (c * (Nat.log2 n + 1)) <= size f.

(** Schema: a superlogarithmic formula-depth lower bound for [fam].  The SAT
    instance is [SATDepthLB]. *)
Definition DepthLBFor (fam : nat -> (nat -> bool) -> bool) : Prop :=
  forall c, exists n, forall f, FormulaComputes f (fam n) ->
    c * (Nat.log2 n + 1) <= depth f.

(** A superpolynomial size lower bound implies a superlogarithmic depth lower bound. *)
Theorem sizeLB_implies_depthLB : forall fam, FormulaSizeLBFor fam -> DepthLBFor fam.
Proof.
  intros fam h c. destruct (h c) as [n hn]. exists n. intros f hf.
  pose proof (hn f hf) as h1. pose proof (size_le_pow_depth f) as h2.
  destruct (Nat.le_gt_cases (c * (Nat.log2 n + 1)) (depth f)) as [ok | lt]; [exact ok|].
  pose proof (two_pow_mono (depth f + 1) (c * (Nat.log2 n + 1)) ltac:(lia)). lia.
Qed.

(** * The obligations on the shared machine model *)

(** Open obligation.  SAT (the language [SAT] of Machines.v) has
    superpolynomial formula size: for every c there is a length n at which
    every formula computing SAT on words of length n has size at least
    2^(c * (log2 n + 1)). *)
Definition SATFormulaSizeLB : Prop :=
  forall c, exists n, forall f, FormulaComputes f (slice SAT n) ->
    2 ^ (c * (Nat.log2 n + 1)) <= size f.

(** Open obligation.  SAT needs superlogarithmic formula depth: for every c
    there is a length n at which every formula computing SAT on words of
    length n has depth at least c * (log2 n + 1). *)
Definition SATDepthLB : Prop :=
  forall c, exists n, forall f, FormulaComputes f (slice SAT n) ->
    c * (Nat.log2 n + 1) <= depth f.

Theorem satFormulaSizeLB_iff_for : SATFormulaSizeLB <-> FormulaSizeLBFor (slice SAT).
Proof. reflexivity. Qed.

Theorem satDepthLB_iff_for : SATDepthLB <-> DepthLBFor (slice SAT).
Proof. reflexivity. Qed.

(** The size obligation implies the depth obligation. *)
Theorem satSizeLB_implies_satDepthLB : SATFormulaSizeLB -> SATDepthLB.
Proof. exact (sizeLB_implies_depthLB (slice SAT)). Qed.

(** Open obligation (the honest target, NP not in NC1-type).  Some language
    with [InNP] needs superlogarithmic formula depth. *)
Definition NPNotInLogDepth : Prop :=
  exists L : Language, InNP L /\
    forall c, exists n, forall f, FormulaComputes f (slice L n) ->
      c * (Nat.log2 n + 1) <= depth f.

(** Conditional theorem (honest conclusion).  With [SATInNP], the depth
    obligation for SAT gives [NPNotInLogDepth]. *)
Theorem npNotInLogDepth_of_satDepthLB : SATInNP -> SATDepthLB -> NPNotInLogDepth.
Proof. intros mem h. exists SAT. split; [exact mem | exact h]. Qed.

Theorem npNotInLogDepth_of_satFormulaSizeLB :
  SATInNP -> SATFormulaSizeLB -> NPNotInLogDepth.
Proof.
  intros mem h. exact (npNotInLogDepth_of_satDepthLB mem (satSizeLB_implies_satDepthLB h)).
Qed.

(** Not known, and not assumed anywhere: every language in P has formulas of
    logarithmic depth (a P in NC1-type statement, open and widely believed
    false).  Stated only to show what a depth lower bound would additionally
    need in order to give P <> NP. *)
Definition PSubsetLogDepth : Prop :=
  forall L : Language, InP L -> exists c, forall n, exists f,
    FormulaComputes f (slice L n) /\ depth f < c * (Nat.log2 n + 1).

(** The gap, made explicit: [SATDepthLB] gives P <> NP only together with
    the unproved [PSubsetLogDepth]. *)
Theorem pNotEqualsNP_of_satDepthLB :
  SATInNP -> PSubsetLogDepth -> SATDepthLB -> PNotEqualsNP.
Proof.
  intros mem hPL h hPNP.
  destruct (hPL SAT (hPNP SAT mem)) as [c hc].
  destruct (h c) as [n hn].
  destruct (hc n) as [f [hf hd]].
  pose proof (hn f hf). lia.
Qed.

(** * Non-vacuity of the lower-bound shapes *)

(** Variables read by a formula, one entry per leaf. *)
Fixpoint vars (f : F) : list nat :=
  match f with
  | Var i => [i]
  | Neg g => vars g
  | Conj g h => vars g ++ vars h
  | Disj g h => vars g ++ vars h
  end.

Theorem vars_length : forall f, length (vars f) = leaves f.
Proof. induction f; simpl; rewrite ?length_app; lia. Qed.

Theorem leaves_le_size : forall f, leaves f <= size f.
Proof. induction f; simpl; lia. Qed.

(** A formula only depends on the variables it reads. *)
Theorem eval_congr : forall f (rho sigma : nat -> bool),
  (forall i, In i (vars f) -> rho i = sigma i) -> eval rho f = eval sigma f.
Proof.
  induction f as [i | g IH | g IHg h IHh | g IHg h IHh]; intros rho sigma hv; simpl in *.
  - apply hv. left. reflexivity.
  - rewrite (IH rho sigma hv). reflexivity.
  - rewrite (IHg rho sigma), (IHh rho sigma); [reflexivity | |];
      intros j hj; apply hv; apply in_or_app; auto.
  - rewrite (IHg rho sigma), (IHh rho sigma); [reflexivity | |];
      intros j hj; apply hv; apply in_or_app; auto.
Qed.

Theorem andRange_true : forall a m, andRange a m (fun _ => true) = true.
Proof. intros a m. induction m; simpl; [reflexivity|]. rewrite IHm. reflexivity. Qed.

Theorem andRange_false : forall a m i (rho : nat -> bool),
  a <= i -> i < a + m -> rho i = false -> andRange a m rho = false.
Proof.
  intros a m i rho h1 h2 hi. induction m; [lia|]. simpl.
  destruct (Nat.eq_dec i (a + m)) as [e | e].
  - subst i. rewrite hi, andb_false_r. reflexivity.
  - rewrite IHm; [reflexivity | lia].
Qed.

(** The AND of the first 2 ^ n variables.  It reads 2 ^ n variables, so it is
    not a function "on n variables"; it only shows that the lower-bound
    shapes can be met. *)
Definition andPow (n : nat) (rho : nat -> bool) : bool := andRange 0 (2 ^ n) rho.

(** Every formula for [andPow n] reads all 2 ^ n variables.  Rocq decides
    membership in [vars f] with [in_dec]; Lean uses a classical case split. *)
Theorem andPow_leaves : forall n f, FormulaComputes f (andPow n) -> 2 ^ n <= leaves f.
Proof.
  intros n f hf. rewrite <- vars_length.
  rewrite <- (length_seq (2 ^ n) 0).
  apply NoDup_incl_length; [apply seq_NoDup|].
  intros i hi. apply in_seq in hi.
  destruct (in_dec Nat.eq_dec i (vars f)) as [yes | no]; [exact yes|].
  exfalso.
  assert (e : eval (fun _ => true) f = eval (fun j => negb (Nat.eqb j i)) f).
  { apply eval_congr. intros j hj.
    destruct (Nat.eqb_spec j i) as [ji | ji]; [subst j; contradiction | reflexivity]. }
  rewrite (hf (fun _ => true)), (hf (fun j => negb (Nat.eqb j i))) in e.
  unfold andPow in e. rewrite andRange_true in e.
  rewrite (andRange_false 0 (2 ^ n) i) in e; [discriminate | lia | lia |].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem mul_succ_le_two_pow : forall c, c * (c + 7 + 1) <= 2 ^ (c + 7).
Proof.
  intro c. pose proof (two_mul_sq_lt_two_pow (c + 7) ltac:(lia)). nia.
Qed.

(** Non-vacuity (true side): [andPow] meets the size lower-bound shape. *)
Theorem andPow_sizeLB : FormulaSizeLBFor andPow.
Proof.
  intro c. exists (2 ^ (c + 7)). intros f hf.
  rewrite Nat.log2_pow2 by lia.
  pose proof (andPow_leaves _ f hf) as h1.
  pose proof (leaves_le_size f) as h2.
  pose proof (two_pow_mono _ _ (mul_succ_le_two_pow c)) as h3.
  lia.
Qed.

(** Non-vacuity (true side): [andPow] meets the depth lower-bound shape. *)
Theorem andPow_depthLB : DepthLBFor andPow.
Proof. exact (sizeLB_implies_depthLB andPow andPow_sizeLB). Qed.

(** Non-vacuity (false side): a family computed by the single leaf [Var 0]
    meets neither shape. *)
Theorem var0_not_depthLB : ~ DepthLBFor (fun _ rho => rho 0).
Proof.
  intro h. destruct (h 1) as [n hn].
  specialize (hn (Var 0) (fun _ => eq_refl)). simpl in hn. lia.
Qed.

Theorem var0_not_sizeLB : ~ FormulaSizeLBFor (fun _ rho => rho 0).
Proof. intro h. exact (var0_not_depthLB (sizeLB_implies_depthLB _ h)). Qed.
