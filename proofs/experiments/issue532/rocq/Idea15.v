(* Issue #532, Idea 15: circuit depth versus size.

   Rocq counterpart of lean/Idea15.lean; theorem names are aligned.

   Formulas over variables, NOT and fan-in-2 AND/OR.  Proved in general:
   depth f < size f < 2^(depth f + 1) and leaves f <= 2^(depth f); the AND
   chain attains depth = size - 1 / 2, the balanced AND tree attains
   size = 2^(depth+1) - 1; for every d both compute the AND of 2^d variables
   with the same size and depths 2^d - 1 versus d; and a superpolynomial
   formula-size lower bound implies a superlogarithmic depth lower bound.

   Verdict: size and depth are distinct resources; even the open obligation
   DepthLB for an explicit NP family would give NP not in NC^1, not P <> NP.
   Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool.

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

Definition Computes (f : F) (g : (nat -> bool) -> bool) : Prop := forall rho, eval rho f = g rho.

(** Open obligation (not assumed): superpolynomial formula size. *)
Definition FormulaSizeLB (fam : nat -> (nat -> bool) -> bool) : Prop :=
  forall c, exists n, forall f, Computes f (fam n) -> 2 ^ (c * (Nat.log2 n + 1)) <= size f.

(** Open obligation (not assumed): superlogarithmic formula depth. *)
Definition DepthLB (fam : nat -> (nat -> bool) -> bool) : Prop :=
  forall c, exists n, forall f, Computes f (fam n) -> c * (Nat.log2 n + 1) <= depth f.

(** A superpolynomial size lower bound implies a superlogarithmic depth lower bound. *)
Theorem sizeLB_implies_depthLB : forall fam, FormulaSizeLB fam -> DepthLB fam.
Proof.
  intros fam h c. destruct (h c) as [n hn]. exists n. intros f hf.
  pose proof (hn f hf) as h1. pose proof (size_le_pow_depth f) as h2.
  destruct (Nat.le_gt_cases (c * (Nat.log2 n + 1)) (depth f)) as [ok | lt]; [exact ok|].
  pose proof (two_pow_mono (depth f + 1) (c * (Nat.log2 n + 1)) ltac:(lia)). lia.
Qed.
