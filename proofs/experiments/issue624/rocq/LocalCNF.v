From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
Import ListNotations.

(** Finite local constraints in the actual CNF and unary encoding. No whole
    configurations, traces, or certificates are enumerated. *)
Module LocalCNF.
Import Complexity Machines.

Theorem evalCNF_append : forall a f g,
  evalCNF a (f ++ g) = andb (evalCNF a f) (evalCNF a g).
Proof.
  intros a f. induction f as [|c f IH]; intro g; simpl; [reflexivity|].
  rewrite IH, andb_assoc. reflexivity.
Qed.

Theorem evalCNF_map : forall (A : Type) a (cs : list A) f,
  evalCNF a (map f cs) = true <-> forall c, In c cs -> evalClause a (f c) = true.
Proof.
  intros A a cs f. induction cs as [|c cs IH]; simpl.
  - split; [intros _ x h; contradiction|intro h; reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [hc ht] x [hx|hx]; [subst; exact hc|auto].
    + intro h. split; [apply h; left; reflexivity|]. intros. apply h. right. assumption.
Qed.

Theorem evalCNF_flatMap : forall (A : Type) a (cs : list A) f,
  evalCNF a (flat_map f cs) = true <-> forall c, In c cs -> evalCNF a (f c) = true.
Proof.
  intros A a cs f. induction cs as [|c cs IH]; simpl.
  - split; [intros _ x h; contradiction|intro h; reflexivity].
  - rewrite evalCNF_append, andb_true_iff, IH. split.
    + intros [hc ht] x [hx|hx]; [subst; exact hc|auto].
    + intro h. split; [apply h; left; reflexivity|]. intros. apply h. right. assumption.
Qed.

Theorem evalClause_map : forall (A : Type) a (cs : list A) f,
  evalClause a (map f cs) = true <-> exists c, In c cs /\ evalLit a (f c) = true.
Proof.
  intros A a cs f. induction cs as [|c cs IH]; simpl.
  - split; [discriminate|]. intros [x [h _]]. contradiction.
  - rewrite orb_true_iff, IH. split.
    + intros [hc|[x [hx he]]]; [exists c; auto|exists x; auto].
    + intros [x [[hx|hx] he]]; [subst; auto|right; exists x; auto].
Qed.

Definition negate (l : Lit) : Lit := mkLit (var l) (negb (pos l)).
Definition implies (premises conclusion : Clause) : Clause :=
  map negate premises ++ conclusion.

Theorem evalLit_negate : forall a l, evalLit a (negate l) = negb (evalLit a l).
Proof.
  intros a [v p]. unfold evalLit, negate. simpl.
  destruct p, (a v); reflexivity.
Qed.

Theorem implies_models : forall a premises conclusion,
  evalClause a (implies premises conclusion) = true <->
    ((forall l, In l premises -> evalLit a l = true) -> evalClause a conclusion = true).
Proof.
  intros a premises conclusion. induction premises as [|l ls IH].
  - simpl. split; [auto|]. intro h. apply h. intros x hx. contradiction.
  - change (orb (evalLit a (negate l)) (evalClause a (implies ls conclusion)) = true <->
      ((forall x, In x (l :: ls) -> evalLit a x = true) -> evalClause a conclusion = true)).
    rewrite evalLit_negate, orb_true_iff, negb_true_iff, IH.
    destruct (evalLit a l) eqn:hl; split.
    + intros [hc|hc]; [discriminate|]. intro h. apply hc. intros. apply h. right. assumption.
    + intro h. right. intro ht. apply h. intros x [hx|hx]; [subst; exact hl|auto].
    + intros _. intro h. specialize (h l (or_introl eq_refl)). congruence.
    + intro h. left. reflexivity.
Qed.

Fixpoint atMostOne (base size : nat) : CNF :=
  match size with
  | 0 => []
  | S n => map (fun i => [mkLit base false; mkLit (base + 1 + i) false]) (seq 0 n) ++
      atMostOne (base + 1) n
  end.
Definition oneHot (base size : nat) : CNF :=
  [map (fun i => mkLit (base + i) true) (seq 0 size)] ++ atMostOne base size.

Lemma negative_pair : forall a u v,
  evalClause a [mkLit u false; mkLit v false] = true <->
    (a u = true -> a v = false).
Proof.
  intros a u v. unfold evalClause, evalLit. simpl.
  destruct (a u), (a v); simpl; intuition congruence.
Qed.

Lemma atMostOne_models : forall a base size,
  evalCNF a (atMostOne base size) = true <->
    forall i, i < size -> forall j, j < size ->
      a (base + i) = true -> a (base + j) = true -> i = j.
Proof.
  intros a base size. revert base. induction size as [|n IH]; intro base.
  - simpl. split; intros; [lia|reflexivity].
  - assert (hp : evalCNF a (atMostOne base (S n)) = true <->
      (forall j, j < n -> a base = true -> a (base + 1 + j) = false) /\
      (forall i, i < n -> forall j, j < n ->
        a (base + 1 + i) = true -> a (base + 1 + j) = true -> i = j)).
    { cbn [atMostOne]. rewrite evalCNF_append, andb_true_iff, evalCNF_map, IH.
      split; intros [hf hr]; split; try exact hr.
      - intros j hj. apply negative_pair. apply hf. apply in_seq. lia.
      - intros j hj. apply negative_pair. apply in_seq in hj. apply hf. lia. }
    rewrite hp. split.
    + intros [hf hr] [|i] hi [|j] hj hai haj; try reflexivity.
      * assert (ha : a (base + 1 + j) = false) by (apply hf; [lia|replace (base + 0) with base in hai by lia; exact hai]).
        replace (base + S j) with (base + 1 + j) in haj by lia. congruence.
      * assert (ha : a (base + 1 + i) = false) by (apply hf; [lia|replace (base + 0) with base in haj by lia; exact haj]).
        replace (base + S i) with (base + 1 + i) in hai by lia. congruence.
      * replace (base + S i) with (base + 1 + i) in hai by lia.
        replace (base + S j) with (base + 1 + j) in haj by lia.
        f_equal. apply hr; auto; lia.
    + intro h. split.
      * intros j hj hb. destruct (a (base + 1 + j)) eqn:ha; [|reflexivity].
        assert (he : 0 = S j).
        { apply h; try lia; replace (base + 0) with base by lia; auto.
          replace (base + S j) with (base + 1 + j) by lia; exact ha. }
        lia.
      * intros i hi j hj hai haj. assert (he : S i = S j).
        { apply h; try lia; [replace (base + S i) with (base + 1 + i) by lia; exact hai|
            replace (base + S j) with (base + 1 + j) by lia; exact haj]. }
        lia.
Qed.

Theorem oneHot_models : forall a base size,
  evalCNF a (oneHot base size) = true <->
    exists v, v < size /\ a (base + v) = true /\
      forall w, w < size -> a (base + w) = true -> w = v.
Proof.
  intros a base size. unfold oneHot.
  rewrite evalCNF_append. cbn [evalCNF]. rewrite andb_true_r, andb_true_iff,
    evalClause_map, atMostOne_models. split.
  - intros [[v [hv hav]] h]. apply in_seq in hv. exists v.
    cbn [evalLit var pos] in hav. unfold evalLit in hav. simpl in hav.
    rewrite Bool.eqb_true_iff in hav.
    split; [lia|]. split; [exact hav|]. intros. apply h; auto; lia.
  - intros [v [hv [hav h]]]. split.
    + exists v. split; [apply in_seq; lia|].
      unfold evalLit. simpl. rewrite Bool.eqb_true_iff. exact hav.
    + intros i hi j hj hai haj. rewrite (h i hi hai), (h j hj haj). reflexivity.
Qed.

Lemma ticks_length : forall n, length (ticks n) = 2 * n.
Proof. induction n; simpl; lia. Qed.

Lemma clause_encoded_size : forall c bound,
  (forall l, In l c -> var l < bound) ->
  length (encodeClause c) <= 2 * (1 + length c * (bound + 1)).
Proof.
  intros c bound. induction c as [|l c IH]; intro h; cbn [encodeClause].
  - simpl. lia.
  - specialize (IH ltac:(intros; apply h; right; assumption)).
    pose proof (h l (or_introl eq_refl)) as hl.
    unfold encodeLit. rewrite length_app, length_app, ticks_length. simpl. nia.
Qed.

Theorem cnf_encoded_size : forall f bound width,
  VarsBelow bound f -> (forall c, In c f -> length c <= width) ->
  length (encodeCNF f) <= 2 * length f * (1 + width * (bound + 1)).
Proof.
  intros f bound width. induction f as [|c f IH]; intros hv hw; cbn [encodeCNF]; [simpl; lia|].
  assert (hc : length (encodeClause c) <= 2 * (1 + length c * (bound + 1))).
  { apply clause_encoded_size. intros. apply hv with c; auto. left. reflexivity. }
  pose proof (hw c (or_introl eq_refl)) as hl.
  specialize (IH ltac:(intros c' hc' l hl'; apply hv with c'; [right; exact hc'|exact hl'])
    ltac:(intros c' hc'; apply hw; right; exact hc')).
  rewrite length_app. simpl length. nia.
Qed.

Lemma atMostOne_length : forall base size, length (atMostOne base size) <= size * size.
Proof.
  intros base size. revert base. induction size; intro base; cbn [atMostOne]; [simpl; lia|].
  rewrite length_app, length_map, length_seq. specialize (IHsize (base + 1)).
  eapply Nat.le_trans; [apply Nat.add_le_mono_l; exact IHsize|]. nia.
Qed.

Lemma atMostOne_bounds : forall base size,
  VarsBelow (base + size) (atMostOne base size) /\
    forall c, In c (atMostOne base size) -> length c <= 2.
Proof.
  intros base size. revert base. induction size as [|n IH]; intro base.
  - unfold VarsBelow. simpl. split; intros; contradiction.
  - destruct (IH (base + 1)) as [hv hw]. split.
    + intros c hc l hl. cbn [atMostOne] in hc. apply in_app_or in hc.
      destruct hc as [hc|hc].
      * apply in_map_iff in hc. destruct hc as [i [he hi]]. subst c.
        apply in_seq in hi. simpl in hl. destruct hl as [he|[he|[]]]; subst l; simpl; lia.
      * specialize (hv c hc l hl). lia.
    + intros c hc. cbn [atMostOne] in hc. apply in_app_or in hc.
      destruct hc as [hc|hc].
      * apply in_map_iff in hc. destruct hc as [i [he hi]]. subst c. simpl. lia.
      * apply hw. exact hc.
Qed.

Theorem oneHot_encoded_size : forall base size,
  length (encodeCNF (oneHot base size)) <=
    2 * (size * size + 1) * (1 + (size + 2) * (base + size + 1)).
Proof.
  intros base size. destruct (atMostOne_bounds base size) as [hv hw].
  assert (hvars : VarsBelow (base + size) (oneHot base size)).
  { intros c hc l hl. unfold oneHot in hc. simpl in hc.
    destruct hc as [he|hc]; [subst c|exact (hv c hc l hl)].
    apply in_map_iff in hl. destruct hl as [i [he hi]]. subst l.
    apply in_seq in hi. simpl. lia. }
  assert (hwidth : forall c, In c (oneHot base size) -> length c <= size + 2).
  { intros c hc. unfold oneHot in hc. simpl in hc. destruct hc as [he|hc].
    - subst c. rewrite length_map, length_seq. lia.
    - specialize (hw c hc). lia. }
  pose proof (cnf_encoded_size _ _ _ hvars hwidth) as h.
  pose proof (atMostOne_length base size) as hl.
  unfold oneHot in h. cbn [app length] in h.
  remember (length (atMostOne base size)) as k in h, hl. clear Heqk.
  eapply Nat.le_trans; [exact h|].
  apply Nat.mul_le_mono_r. nia.
Qed.

End LocalCNF.
