(* Issue #532, Idea 38: relativization audit (oracle query lower bound).

   Rocq counterpart of ../lean/Idea38.lean (same theorem names and content).
   Deterministic oracle computations are adaptive decision trees over an oracle
   O : nat -> bool. A tree of depth < N cannot distinguish the all-false oracle
   from some oracle that is true at exactly one position j < N, so it cannot
   decide "exists j < N, O j = true" (the combinatorial core of Baker-Gill-Solovay).
   The bound is exact (orTree), a guessed position is verified with one query,
   and polynomial-depth families fail on 2^n positions (bgs_core).
   Abstractly, a relativizing proof method settles no statement that holds for
   one oracle and fails for another. The BGS oracle constructions themselves
   are not formalized. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia Classical_Prop.
Import ListNotations.

Theorem tested : exists property : bool -> Prop, property false /\ ~ property true.
Proof. exists (fun oracle => oracle = false). split; [reflexivity | discriminate]. Qed.

(* Decision trees with oracle queries. *)

Inductive Tree : Type :=
| leaf (b : bool)
| query (i : nat) (t0 t1 : Tree).

Fixpoint eval (O : nat -> bool) (T : Tree) : bool :=
  match T with
  | leaf b => b
  | query i t0 t1 => if O i then eval O t1 else eval O t0
  end.

Fixpoint depth (T : Tree) : nat :=
  match T with
  | leaf _ => 0
  | query _ t0 t1 => S (Nat.max (depth t0) (depth t1))
  end.

Fixpoint falsePath (T : Tree) : list nat :=
  match T with
  | leaf _ => []
  | query i t0 _ => i :: falsePath t0
  end.

Definition allFalse : nat -> bool := fun _ => false.

Definition single (j : nat) : nat -> bool := fun i => Nat.eqb i j.

Theorem falsePath_length : forall T, length (falsePath T) <= depth T.
Proof.
  induction T as [b | i t0 IH0 t1 IH1]; simpl; [lia|].
  pose proof (Nat.le_max_l (depth t0) (depth t1)). lia.
Qed.

Theorem eval_single_of_not_mem : forall T j,
  ~ In j (falsePath T) -> eval (single j) T = eval allFalse T.
Proof.
  induction T as [b | i t0 IH0 t1 IH1]; intros j Hj; simpl; [reflexivity|].
  simpl in Hj.
  assert (Hij : Nat.eqb i j = false).
  { apply Nat.eqb_neq. intro E. apply Hj. left. exact E. }
  unfold single at 1. rewrite Hij. unfold allFalse at 1.
  apply IH0. intro H. apply Hj. right. exact H.
Qed.

Theorem exists_not_mem : forall N (L : list nat),
  length L < N -> exists j, j < N /\ ~ In j L.
Proof.
  induction N as [|N IH]; intros L HL; [lia|].
  destruct (In_dec Nat.eq_dec N L) as [HN | HN].
  - pose proof (remove_length_lt Nat.eq_dec L N HN) as Hlen.
    destruct (IH (remove Nat.eq_dec N L) ltac:(lia)) as [j [Hj HjL]].
    exists j. split; [lia|].
    intro Hin. apply HjL. apply in_in_remove; [lia | exact Hin].
  - exists N. split; [lia | exact HN].
Qed.

(* Shallow trees miss a position. *)
Theorem shallow_tree_misses : forall T N,
  depth T < N -> exists j, j < N /\ eval allFalse T = eval (single j) T.
Proof.
  intros T N H.
  pose proof (falsePath_length T).
  destruct (exists_not_mem N (falsePath T) ltac:(lia)) as [j [Hj HjL]].
  exists j. split; [exact Hj|].
  symmetry. apply eval_single_of_not_mem. exact HjL.
Qed.

(* Query lower bound (BGS core). *)
Theorem no_shallow_tree_decides_or : forall T N,
  depth T < N ->
  ~ (forall O : nat -> bool, eval O T = true <-> exists j, j < N /\ O j = true).
Proof.
  intros T N H Hdec.
  destruct (shallow_tree_misses T N H) as [j [Hj Heq]].
  assert (H1 : eval (single j) T = true).
  { apply Hdec. exists j. split; [exact Hj|]. unfold single. apply Nat.eqb_refl. }
  assert (H0 : eval allFalse T <> true).
  { intro Ht. apply Hdec in Ht. destruct Ht as [k [_ Hk]]. discriminate Hk. }
  apply H0. rewrite Heq. exact H1.
Qed.

(* The bound is exact, and one nondeterministic query suffices. *)

Fixpoint orTree (N : nat) : Tree :=
  match N with
  | 0 => leaf false
  | S N' => query N' (orTree N') (leaf true)
  end.

Theorem orTree_depth : forall N, depth (orTree N) = N.
Proof.
  induction N as [|N IH]; simpl; [reflexivity|].
  rewrite IH. f_equal. apply Nat.max_l. lia.
Qed.

Theorem orTree_correct : forall (O : nat -> bool) N,
  eval O (orTree N) = true <-> exists j, j < N /\ O j = true.
Proof.
  intros O N. induction N as [|N IH]; simpl.
  - split; [discriminate | intros [j [Hj _]]; lia].
  - destruct (O N) eqn:HN.
    + split; [intros _; exists N; split; [lia | exact HN] | reflexivity].
    + rewrite IH. split.
      * intros [j [Hj HOj]]. exists j. split; [lia | exact HOj].
      * intros [j [Hj HOj]]. destruct (Nat.eq_dec j N) as [E | E].
        -- subst j. rewrite HN in HOj. discriminate.
        -- exists j. split; [lia | exact HOj].
Qed.

Theorem verifier_one_query : forall (O : nat -> bool) N,
  (exists j, j < N /\ O j = true) <->
  exists j, j < N /\ eval O (query j (leaf false) (leaf true)) = true.
Proof.
  intros O N. split.
  - intros [j [Hj HOj]]. exists j. split; [exact Hj|]. simpl. rewrite HOj. reflexivity.
  - intros [j [Hj Hev]]. exists j. split; [exact Hj|]. simpl in Hev.
    destruct (O j); [reflexivity | discriminate].
Qed.

(* Polynomial depth against 2^n positions. *)

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

(* BGS core, polynomial form. *)
Theorem bgs_core : forall (trees : nat -> Tree) c k,
  (forall n, depth (trees n) <= c * (n + 1) ^ k) ->
  exists n, ~ (forall O : nat -> bool,
    eval O (trees n) = true <-> exists j, j < 2 ^ n /\ O j = true).
Proof.
  intros trees c k Hdepth.
  exists (2 ^ (2 * (c + k) + 1)).
  apply no_shallow_tree_decides_or.
  eapply Nat.le_lt_trans; [apply Hdepth|].
  apply exp_beats_poly. lia.
Qed.

(* Relativizing proof methods. *)

Definition Relativizing (Proves : ((nat -> bool) -> Prop) -> Prop) : Prop :=
  forall S, Proves S -> forall O, S O.

Theorem relativizing_cannot_prove : forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  Relativizing Proves -> forall (S : (nat -> bool) -> Prop) O, ~ S O -> ~ Proves S.
Proof. intros Proves Hrel S O HO HS. apply HO. apply (Hrel S HS O). Qed.

(* BGS meta-theorem (abstract). *)
Theorem relativizing_cannot_decide : forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  Relativizing Proves -> forall (S : (nat -> bool) -> Prop) (A B : nat -> bool),
  S A -> ~ S B -> ~ Proves S /\ ~ Proves (fun O => ~ S O).
Proof.
  intros Proves Hrel S A B HA HB. split.
  - apply (relativizing_cannot_prove Proves Hrel S B HB).
  - apply (relativizing_cannot_prove Proves Hrel (fun O => ~ S O) A).
    intro H. apply H. exact HA.
Qed.

(* Open obligation: a nonrelativizing ingredient. *)
Definition NonrelativizingIngredient (Proves : ((nat -> bool) -> Prop) -> Prop) : Prop :=
  exists S O, Proves S /\ ~ S O.

Theorem nonrelativizing_needed : forall (Proves : ((nat -> bool) -> Prop) -> Prop)
  (S : (nat -> bool) -> Prop) (A B : nat -> bool),
  S A -> ~ S B -> (Proves S \/ Proves (fun O => ~ S O)) ->
  NonrelativizingIngredient Proves.
Proof.
  intros Proves S A B HA HB [H | H].
  - exists S, B. split; assumption.
  - exists (fun O => ~ S O), A. split; [exact H|]. intro H'. apply H'. exact HA.
Qed.

(* NonrelativizingIngredient is exactly the failure of Relativizing. The backward
   direction uses excluded middle (NNPP from Classical_Prop), as the Lean proof
   uses Classical.byContradiction; every other theorem in this file is constructive. *)
Theorem nonrelativizing_iff : forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  NonrelativizingIngredient Proves <-> ~ Relativizing Proves.
Proof.
  intros Proves. split.
  - intros [S [O [HS HO]]] Hrel. apply HO. apply (Hrel S HS O).
  - intros Hnot. apply NNPP. intros Hno. apply Hnot. intros S HS O.
    apply NNPP. intros HO. apply Hno. exists S, O. split; assumption.
Qed.

Example orTree_check : eval (single 1) (orTree 2) = true.
Proof. reflexivity. Qed.
