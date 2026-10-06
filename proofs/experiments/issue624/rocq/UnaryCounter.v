From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
Import ListNotations.

(** One finite input-retaining unary counter block. Its nine-state table is
    independent of the word and counter value. Every scan and write is charged
    in the shared Reaches semantics. *)
Module UnaryCounter.
Import Complexity Machines.

Definition counter : Machine := {| program :=
  [[move 1 blank right; halt false; halt false; halt false];
   [halt false; move 2 blank left; move 3 blank left; move 9 separator left];
   [move 4 zero right; halt false; halt false; halt false];
   [move 4 one right; halt false; halt false; halt false];
   [move 5 blank right; halt false; halt false; halt false];
   [halt false; move 5 zero right; move 5 one right; move 6 separator right];
   [move 7 one left; halt false; move 6 one right; halt false];
   [halt false; halt false; move 7 one left; move 8 separator left];
   [move 0 blank stay; move 8 zero left; move 8 one left; halt false]] |}.
Definition ticks (k : nat) : list Symbol := repeat one k.
Definition cursor (l : list Symbol) (x : Word) (k : nat) : Config :=
  {| state := 0; tapeLeft := l; tapeHead := blank;
     tapeRight := map ofBool x ++ separator :: ticks k |}.
Definition finished (l : list Symbol) (x : Word) (k : nat) : Config :=
  {| state := 9; tapeLeft := rev (map ofBool x) ++ l; tapeHead := blank;
     tapeRight := separator :: ticks (k + length x) |}.
Definition countTime (n k : nat) : nat := n * (2 * (n + k) + 6) + 2.
Definition counterPolynomial : Polynomial := {| coefficient := 8; degree := 2 |}.

Lemma ticks_reverse : forall k, rev (ticks k) = ticks k.
Proof. intros. unfold ticks. apply rev_repeat. Qed.
Lemma ticks_length : forall k, length (ticks k) = k.
Proof. intros. unfold ticks. apply repeat_length. Qed.
Lemma ticks_snoc : forall k, ticks k ++ [one] = ticks (k + 1).
Proof. intros. unfold ticks. rewrite repeat_app. reflexivity. Qed.

Lemma scan_input_right : forall x l r,
  Reaches counter (scanConfig 5 l (map ofBool x ++ r)) (length x)
    (scanConfig 5 (rev (map ofBool x) ++ l) r).
Proof.
  intros. rewrite <- (length_map ofBool x). apply scan_right.
  intros a ha. apply in_map_iff in ha. destruct ha as [b [<- _]]. destruct b; reflexivity.
Qed.
Lemma scan_input_left : forall x l r,
  Reaches counter (scanLeftConfig 8 r (rev (map ofBool x) ++ l)) (length x)
    (scanLeftConfig 8 (map ofBool x ++ r) l).
Proof.
  intros. pose proof (scan_left counter 8 (rev (map ofBool x)) r l) as h.
  rewrite length_rev, length_map, rev_involutive in h. apply h.
  intros a ha. apply (proj2 (in_rev _ _)) in ha. apply in_map_iff in ha.
  destruct ha as [b [<- _]]. destruct b; reflexivity.
Qed.
Lemma scan_ticks_right : forall k l,
  Reaches counter (scanConfig 6 l (ticks k)) k
    {| state := 6; tapeLeft := ticks k ++ l; tapeHead := blank; tapeRight := [] |}.
Proof.
  intros. pose proof (scan_right counter 6 (ticks k) l []) as h.
  rewrite app_nil_r, ticks_reverse, ticks_length in h. apply h.
  intros a ha. apply repeat_spec in ha. subst a. reflexivity.
Qed.
Lemma scan_ticks_left : forall k l,
  Reaches counter (scanLeftConfig 7 [one] (ticks k ++ separator :: l)) k
    {| state := 7; tapeLeft := l; tapeHead := separator; tapeRight := ticks (k + 1) |}.
Proof.
  intros. pose proof (scan_left counter 7 (ticks k) [one] (separator :: l)) as h.
  rewrite ticks_reverse, ticks_snoc, ticks_length in h. apply h.
  intros a ha. apply repeat_spec in ha. subst a. reflexivity.
Qed.

Theorem counter_cycle : forall l b x k,
  Reaches counter (cursor l (b :: x) k) (8 + 2 * length x + 2 * k)
    (cursor (ofBool b :: l) x (k + 1)).
Proof.
  intros l b x k. set (p := ofBool b :: l). set (r := map ofBool x).
  set (back := rev r ++ blank :: p).
  assert (hstart : Reaches counter (cursor l (b :: x) k) 3
    {| state := 4; tapeLeft := p; tapeHead := blank; tapeRight := r ++ separator :: ticks k |}).
  { destruct b.
    - eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|].
      eapply reaches_next; [reflexivity|apply reaches_refl].
    - eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|].
      eapply reaches_next; [reflexivity|apply reaches_refl]. }
  assert (hs : step counter
    {| state := 4; tapeLeft := p; tapeHead := blank; tapeRight := r ++ separator :: ticks k |} =
    inr (scanConfig 5 (blank :: p) (r ++ separator :: ticks k))).
  { destruct x; reflexivity. }
  pose proof (scan_input_right x (blank :: p) (separator :: ticks k)) as hr.
  assert (hsep : step counter
    {| state := 5; tapeLeft := back; tapeHead := separator; tapeRight := ticks k |} =
    inr (scanConfig 6 (separator :: back) (ticks k))).
  { destruct k; reflexivity. }
  pose proof (scan_ticks_right k (separator :: back)) as hi.
  assert (hadd : step counter
    {| state := 6; tapeLeft := ticks k ++ separator :: back; tapeHead := blank; tapeRight := [] |} =
    inr (scanLeftConfig 7 [one] (ticks k ++ separator :: back))).
  { destruct k; reflexivity. }
  pose proof (scan_ticks_left k back) as hb.
  assert (hreturn : step counter
    {| state := 7; tapeLeft := back; tapeHead := separator; tapeRight := ticks (k + 1) |} =
    inr (scanLeftConfig 8 (separator :: ticks (k + 1)) back)).
  { destruct back; reflexivity. }
  pose proof (scan_input_left x (blank :: p) (separator :: ticks (k + 1))) as hl.
  assert (hend : step counter
    {| state := 8; tapeLeft := p; tapeHead := blank; tapeRight := r ++ separator :: ticks (k + 1) |} =
    inr (cursor p x (k + 1))) by reflexivity.
  replace (8 + 2 * length x + 2 * k) with
    (3 + S (length x + S (k + S (k + S (length x + 1))))) by lia.
  eapply reaches_trans; [exact hstart|]. eapply reaches_next; [exact hs|].
  eapply reaches_trans; [exact hr|]. eapply reaches_next; [exact hsep|].
  eapply reaches_trans; [exact hi|]. eapply reaches_next; [exact hadd|].
  eapply reaches_trans; [exact hb|]. eapply reaches_next; [exact hreturn|].
  eapply reaches_trans; [exact hl|]. eapply reaches_next; [exact hend|apply reaches_refl].
Qed.

Theorem counter_reaches : forall l x k,
  Reaches counter (cursor l x k) (countTime (length x) k) (finished l x k).
Proof.
  intros l x. revert l. induction x as [|b x IH]; intros l k.
  - unfold countTime, cursor, finished. cbn [length map rev app]. rewrite Nat.add_0_r.
    eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|apply reaches_refl].
  - assert (ht : countTime (length (b :: x)) k =
      (8 + 2 * length x + 2 * k) + countTime (length x) (k + 1)).
    { unfold countTime. simpl length. nia. }
    rewrite ht. eapply reaches_trans; [apply counter_cycle|].
    specialize (IH (ofBool b :: l) (k + 1)).
    unfold finished in *. cbn [map rev length] in *. rewrite <- app_assoc. cbn [app].
    replace (k + S (length x)) with (k + 1 + length x) by lia. exact IH.
Qed.
Theorem countTime_polynomial : forall n k,
  countTime n k <= evalPoly counterPolynomial (n + k).
Proof. intros. unfold countTime, evalPoly, counterPolynomial. simpl. nia. Qed.
Theorem counter_append : forall next l x k,
  Reaches (appendMachine counter next) (cursor l x k) (countTime (length x) k)
    (finished l x k).
Proof. intros. apply reaches_append. apply counter_reaches. Qed.

Definition prepare : Machine := {| program :=
  [[move 4 separator left; move 1 zero left; move 1 one left; halt false];
   [move 2 blank right; halt false; halt false; halt false];
   [move 3 separator left; move 2 zero right; move 2 one right; halt false];
   [move 7 blank stay; move 3 zero left; move 3 one left; halt false];
   [move 5 blank stay; halt false; halt false; halt false];
   [move 6 blank stay; halt false; halt false; halt false];
   [move 7 blank stay; halt false; halt false; halt false]] |}.
Theorem prepare_reaches : forall x,
  Reaches prepare (initial x) (2 * length x + 4) (shiftConfig 7 (cursor [] x 0)).
Proof.
  intros [|b x].
  - eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|].
    eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|apply reaches_refl].
  - set (r := map ofBool (b :: x)).
    assert (hs : Reaches prepare (initial (b :: x)) 2 (scanConfig 2 [blank] r)).
    { destruct b.
      - eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|apply reaches_refl].
      - eapply reaches_next; [reflexivity|]. eapply reaches_next; [reflexivity|apply reaches_refl]. }
    assert (hf : Reaches prepare (scanConfig 2 [blank] r) (length (b :: x))
      {| state := 2; tapeLeft := rev r ++ [blank]; tapeHead := blank; tapeRight := [] |}).
    { pose proof (scan_right prepare 2 r [blank] []) as h.
      rewrite app_nil_r in h. unfold r in h. rewrite length_map in h. apply h.
      intros a ha. apply in_map_iff in ha. destruct ha as [c [<- _]]. destruct c; reflexivity. }
    assert (ha : step prepare
      {| state := 2; tapeLeft := rev r ++ [blank]; tapeHead := blank; tapeRight := [] |} =
      inr (scanLeftConfig 3 [separator] (rev r ++ [blank]))).
    { destruct (rev r ++ [blank]); reflexivity. }
    assert (hb : Reaches prepare (scanLeftConfig 3 [separator] (rev r ++ [blank])) (length (b :: x))
      {| state := 3; tapeLeft := []; tapeHead := blank; tapeRight := r ++ [separator] |}).
    { pose proof (scan_left prepare 3 (rev r) [separator] [blank]) as h.
      rewrite length_rev, rev_involutive in h. unfold r in h. rewrite length_map in h. apply h.
      intros a ha'. apply (proj2 (in_rev _ _)) in ha'. apply in_map_iff in ha'.
      destruct ha' as [c [<- _]]. destruct c; reflexivity. }
    assert (hh : step prepare
      {| state := 3; tapeLeft := []; tapeHead := blank; tapeRight := r ++ [separator] |} =
      inr (shiftConfig 7 (cursor [] (b :: x) 0))) by reflexivity.
    replace (2 * length (b :: x) + 4) with (2 + (length (b :: x) + S (length (b :: x) + 1))) by lia.
    eapply reaches_trans; [exact hs|]. eapply reaches_trans; [exact hf|].
    eapply reaches_next; [exact ha|]. eapply reaches_trans; [exact hb|].
    eapply reaches_next; [exact hh|apply reaches_refl].
Qed.

Definition countedInput : Machine := appendMachine prepare counter.
Definition inputTime (n : nat) : nat := 2 * n + 4 + countTime n 0.
Definition inputPolynomial : Polynomial := {| coefficient := 12; degree := 2 |}.
Theorem countedInput_reaches : forall x,
  Reaches countedInput (initial x) (inputTime (length x)) (shiftConfig 7 (finished [] x 0)).
Proof.
  intros. unfold countedInput, inputTime. eapply reaches_trans.
  - apply reaches_append. apply prepare_reaches.
  - apply reaches_append_right. apply counter_reaches.
Qed.
Theorem inputTime_polynomial : forall n, inputTime n <= evalPoly inputPolynomial n.
Proof. intros. unfold inputTime, countTime, evalPoly, inputPolynomial. simpl. nia. Qed.

End UnaryCounter.
