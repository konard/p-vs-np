From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue532.rocq Require Import CircuitModel.
Import ListNotations.

Module NandCompiler.

Inductive Expr := input (index : nat) | lit (value : bool) | nand (a b : Expr).

Fixpoint eval (x : list bool) (e : Expr) : bool :=
  match e with
  | input i => wire x i
  | lit b => b
  | nand a b => negb (eval x a && eval x b)
  end.

Fixpoint Bounded (n : nat) (e : Expr) : Prop :=
  match e with
  | input i => i < n
  | lit _ => True
  | nand a b => Bounded n a /\ Bounded n b
  end.

(** Exact gate charge, including constant generation from an input wire. *)
Fixpoint cost (e : Expr) : nat :=
  match e with
  | input _ => 0
  | lit true => 2
  | lit false => 3
  | nand a b => cost a + cost b + 1
  end.

(** Compilation takes syntax and a wire count, never an input or its answer. *)
Fixpoint compile (n : nat) (e : Expr) : Circuit * nat :=
  match e with
  | input i => ([], i)
  | lit true => ([(0,0); (0,n)], n+1)
  | lit false => ([(0,0); (0,n); (n+1,n+1)], n+2)
  | nand a b =>
      let '(A,i) := compile n a in
      let '(B,j) := compile (n + length A) b in
      (A ++ B ++ [(i,j)], n + length A + length B)
  end.

Lemma wires_append : forall x A B,
  wires x (A ++ B) = wires (wires x A) B.
Proof.
  intros x A. revert x. induction A as [|[i j] A IH]; intros; simpl; auto.
Qed.

Lemma wires_length : forall x C,
  length (wires x C) = length x + length C.
Proof.
  intros x C. revert x. induction C as [|[i j] C IH]; intros; simpl.
  - lia.
  - rewrite IH, length_app. simpl. lia.
Qed.

Lemma wires_preserve : forall x C i, i < length x ->
  wire (wires x C) i = wire x i.
Proof.
  intros x C. revert x. induction C as [|[a b] C IH]; intros x i hi; simpl.
  - reflexivity.
  - rewrite IH by (rewrite length_app; simpl; lia).
    apply wire_append_lt. exact hi.
Qed.

Lemma WFfrom_append : forall n A B,
  WFfrom n (A ++ B) <-> WFfrom n A /\ WFfrom (n + length A) B.
Proof.
  intros n A. revert n. induction A as [|[i j] A IH]; intros; simpl.
  - rewrite Nat.add_0_r. tauto.
  - rewrite IH. replace (n + S (length A)) with (n + 1 + length A) by lia.
    tauto.
Qed.

Lemma bounded_mono : forall a n k, Bounded n a -> n <= k -> Bounded k a.
Proof.
  induction a; simpl; intros n k h hn.
  - lia.
  - exact I.
  - destruct h as [h1 h2]. split; [eapply IHa1|eapply IHa2]; eauto.
Qed.

Lemma eval_preserve : forall a x C, Bounded (length x) a ->
  eval (wires x C) a = eval x a.
Proof.
  induction a; intros x C h; simpl in *.
  - apply wires_preserve. exact h.
  - reflexivity.
  - rewrite IHa1, IHa2 by tauto. reflexivity.
Qed.

Lemma compile_cost : forall a n, length (fst (compile n a)) = cost a.
Proof.
  induction a; intros n; simpl; try reflexivity.
  - destruct value; reflexivity.
  - destruct (compile n a1) as [A i] eqn:ha.
    destruct (compile (n + length A) a2) as [B j] eqn:hb. simpl.
    pose proof (IHa1 n) as h1. rewrite ha in h1. simpl in h1.
    pose proof (IHa2 (n + length A)) as h2. rewrite hb in h2. simpl in h2.
    rewrite !length_app. simpl. lia.
Qed.

Theorem compile_WF : forall a n, 0 < n -> Bounded n a ->
  WFfrom n (fst (compile n a)) /\
  snd (compile n a) < n + length (fst (compile n a)).
Proof.
  induction a; intros n hn h; simpl in *.
  - split; auto. lia.
  - destruct value; simpl; intuition lia.
  - destruct (compile n a1) as [A i] eqn:ha.
    destruct (compile (n + length A) a2) as [B j] eqn:hb. simpl.
    destruct (IHa1 n hn (proj1 h)) as [hwa hi]. rewrite ha in hwa,hi. simpl in hwa,hi.
    assert (hbn : Bounded (n + length A) a2) by
      (eapply bounded_mono; [exact (proj2 h)|lia]).
    destruct (IHa2 (n + length A) ltac:(lia) hbn) as [hwb hj].
    rewrite hb in hwb,hj. simpl in hwb,hj.
    split.
    + rewrite !WFfrom_append. simpl.
      intuition lia.
    + rewrite !length_app. simpl. lia.
Qed.

Theorem compile_correct : forall a x, 0 < length x -> Bounded (length x) a ->
  wire (wires x (fst (compile (length x) a))) (snd (compile (length x) a)) = eval x a.
Proof.
  induction a; intros x hx h; simpl in h |- *.
  - reflexivity.
  - destruct value; simpl.
    + replace (length x + 1) with
        (length (x ++ [negb (wire x 0 && wire x 0)])) by (rewrite length_app; simpl; lia).
      rewrite wire_append_self, wire_append_lt by exact hx.
      rewrite wire_append_self. destruct (wire x 0); reflexivity.
    + set (a := negb (wire x 0 && wire x 0)).
      set (b := negb (wire (x ++ [a]) 0 && wire (x ++ [a]) (length x))).
      replace (length x + 2) with (length ((x ++ [a]) ++ [b]))
        by (rewrite !length_app; simpl; lia).
      rewrite wire_append_self.
      replace (length x + 1) with (length (x ++ [a]))
        by (rewrite length_app; simpl; lia).
      rewrite wire_append_self. unfold b.
      rewrite wire_append_lt by exact hx. rewrite wire_append_self.
      unfold a. destruct (wire x 0); reflexivity.
  - destruct (compile (length x) a1) as [A i] eqn:ha.
    destruct (compile (length x + length A) a2) as [B j] eqn:hb. simpl.
    rewrite !wires_append. simpl.
    set (y := wires x A).
    assert (hy : length y = length x + length A) by apply wires_length.
    replace (length x + length A + length B) with (length (wires y B))
      by (rewrite wires_length, hy; reflexivity).
    rewrite wire_append_self.
    destruct (compile_WF a1 (length x) hx (proj1 h)) as [_ hi].
    rewrite ha in hi. simpl in hi.
    rewrite wires_preserve by (rewrite hy; exact hi).
    pose proof (IHa1 x hx (proj1 h)) as ea. rewrite ha in ea. simpl in ea.
    assert (hby : Bounded (length y) a2) by
      (eapply bounded_mono; [exact (proj2 h)|rewrite hy; lia]).
    pose proof (IHa2 y ltac:(rewrite hy; lia) hby) as eb.
    rewrite hy, hb in eb. simpl in eb.
    change (wire y i = eval x a1) in ea.
    rewrite ea, eb. unfold y. rewrite eval_preserve by tauto. reflexivity.
Qed.

Definition neg (a : Expr) : Expr := nand a a.
Definition conj (a b : Expr) : Expr := neg (nand a b).
Definition disj (a b : Expr) : Expr := nand (neg a) (neg b).
Definition mux (s a b : Expr) : Expr := nand (nand s a) (nand (neg s) b).

Lemma eval_mux : forall x s a b,
  eval x (mux s a b) = if eval x s then eval x a else eval x b.
Proof.
  intros. unfold mux, neg. simpl.
  destruct (eval x s), (eval x a), (eval x b); reflexivity.
Qed.

Fixpoint compileMany (n : nat) (es : list Expr) : Circuit * list nat :=
  match es with
  | [] => ([], [])
  | a :: rest =>
      let '(A,i) := compile n a in
      let '(B,js) := compileMany (n + length A) rest in
      (A ++ B, i :: js)
  end.

Definition totalCost (es : list Expr) : nat := fold_right Nat.add 0 (map cost es).

Lemma compileMany_cost : forall es n,
  length (fst (compileMany n es)) = totalCost es.
Proof.
  induction es as [|a es IH]; intros n; simpl; [reflexivity|].
  destruct (compile n a) as [A i] eqn:ha.
  destruct (compileMany (n + length A) es) as [B js] eqn:hb. simpl.
  pose proof (compile_cost a n) as h1. rewrite ha in h1. simpl in h1.
  pose proof (IH (n + length A)) as h2. rewrite hb in h2. simpl in h2.
  rewrite length_app, h1, h2. reflexivity.
Qed.

Theorem compileMany_WF : forall es n, 0 < n ->
  (forall a, In a es -> Bounded n a) ->
  WFfrom n (fst (compileMany n es)) /\
  forall i, In i (snd (compileMany n es)) ->
    i < n + length (fst (compileMany n es)).
Proof.
  induction es as [|a es IH]; intros n hn he; simpl.
  - split; [exact I|intros i hi; contradiction].
  - destruct (compile n a) as [A i] eqn:ha.
    destruct (compileMany (n + length A) es) as [B js] eqn:hb. simpl.
    assert (hea : Bounded n a) by (apply he; simpl; auto).
    destruct (compile_WF a n hn hea) as [hwa hi]. rewrite ha in hwa,hi. simpl in hwa,hi.
    assert (hes : forall e, In e es -> Bounded (n + length A) e).
    { intros e hee. eapply bounded_mono; [apply he; simpl; auto|lia]. }
    destruct (IH (n + length A) ltac:(lia) hes) as [hwb hjs].
    rewrite hb in hwb,hjs. simpl in hwb,hjs.
    split.
    + apply WFfrom_append. auto.
    + intros j [hj|hj]; rewrite length_app.
      * subst j. lia.
      * specialize (hjs j hj). lia.
Qed.

Theorem compileMany_correct : forall es x, 0 < length x ->
  (forall a, In a es -> Bounded (length x) a) ->
  map (wire (wires x (fst (compileMany (length x) es))))
    (snd (compileMany (length x) es)) = map (eval x) es.
Proof.
  induction es as [|a es IH]; intros x hx he; simpl; [reflexivity|].
  destruct (compile (length x) a) as [A i] eqn:ha.
  destruct (compileMany (length x + length A) es) as [B js] eqn:hb. simpl.
  rewrite wires_append. simpl.
  set (y := wires x A).
  assert (hy : length y = length x + length A) by apply wires_length.
  assert (hea : Bounded (length x) a) by (apply he; simpl; auto).
  destruct (compile_WF a (length x) hx hea) as [_ hi].
  rewrite ha in hi. simpl in hi.
  rewrite wires_preserve by (rewrite hy; exact hi).
  pose proof (compile_correct a x hx hea) as ea. rewrite ha in ea. simpl in ea.
  change (wire y i = eval x a) in ea. rewrite ea.
  assert (hes : forall e, In e es -> Bounded (length y) e).
  { intros e hee. eapply bounded_mono; [apply he; simpl; auto|rewrite hy; lia]. }
  pose proof (IH y ltac:(rewrite hy; lia) hes) as hs.
  rewrite hy,hb in hs. simpl in hs. rewrite hs. f_equal.
  apply map_ext_in. intros e hee. unfold y. apply eval_preserve.
  apply he. simpl. auto.
Qed.

Lemma compileMany_outputs_length : forall es n,
  length (snd (compileMany n es)) = length es.
Proof.
  induction es; intros n; [reflexivity|]. cbn [compileMany].
  destruct (compile n a) as [A i].
  destruct (compileMany (n + length A) es) as [B js] eqn:hs. cbn [snd length].
  pose proof (IHes (n + length A)). rewrite hs in H. cbn [snd] in H. lia.
Qed.

End NandCompiler.
