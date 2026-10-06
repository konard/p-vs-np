From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
Import ListNotations.

(** A finite-table output primitive, with charged erasure, writing, and head
    restoration. This is not the input-dependent Cook--Levin reduction. *)
Module ConstantEmitter.
Import Complexity Machines.

Definition symbols : list Symbol := [blank; zero; one; separator].
Definition fixedRow (q : nat) (w : Symbol) (d : Direction) : list Instruction :=
  map (fun _ => move q w d) symbols.
Definition keepRow (q : nat) (d : Direction) : list Instruction :=
  map (fun a => move q a d) symbols.

Fixpoint writeRows (base : nat) (w : Word) : list (list Instruction) :=
  match w with
  | [] => []
  | b :: rest => fixedRow (base + 1) (ofBool b) right :: writeRows (base + 1) rest
  end.
Fixpoint returnRows (base k : nat) : list (list Instruction) :=
  match k with
  | 0 => []
  | S k => keepRow (base + 1) left :: returnRows (base + 1) k
  end.
Definition setupRows : list (list Instruction) :=
  [fixedRow 1 separator right;
   [move 2 blank left; move 1 blank right; move 1 blank right; move 1 blank right];
   [move 2 blank left; move 2 zero left; move 2 one left; move 3 separator stay];
   fixedRow 4 blank stay].
Definition emitter (w : Word) : Machine :=
  {| program := (setupRows ++ writeRows 4 w) ++ returnRows (4 + length w) (length w) |}.
Definition emitterPolynomial (w : Word) : Polynomial :=
  {| coefficient := 4 + 2 * length w; degree := 1 |}.

Lemma writeRows_length : forall base w, length (writeRows base w) = length w.
Proof. intros base w. revert base. induction w; intro base; simpl; auto. Qed.
Lemma returnRows_length : forall base k, length (returnRows base k) = k.
Proof. intros base k. revert base. induction k; intro base; simpl; auto. Qed.

Theorem emitter_states : forall w, length (program (emitter w)) = 4 + 2 * length w.
Proof.
  intro w. unfold emitter. cbn [program]. repeat rewrite length_app.
  rewrite writeRows_length, returnRows_length. cbn [setupRows length]. lia.
Qed.

Lemma setup_instr : forall w a,
  instruction (emitter w) 0 a = move 1 separator right /\
  instruction (emitter w) 1 blank = move 2 blank left /\
  instruction (emitter w) 2 blank = move 2 blank left /\
  instruction (emitter w) 2 separator = move 3 separator stay /\
  instruction (emitter w) 3 a = move 4 blank stay.
Proof. intros w a. destruct a; repeat split; reflexivity. Qed.
Lemma erase_instr : forall w b,
  instruction (emitter w) 1 (ofBool b) = move 1 blank right.
Proof. intros w b. destruct b; reflexivity. Qed.

Lemma writeRows_get : forall w base i, i < length w ->
  nth_error (writeRows base w) i =
    Some (fixedRow (base + i + 1) (ofBool (nth i w false)) right).
Proof.
  intro w. induction w as [|b w IH]; intros base [|i] hi; simpl in hi; try lia.
  - cbn [writeRows nth_error nth]. replace (base + 0 + 1) with (base + 1) by lia. reflexivity.
  - cbn [writeRows nth_error nth]. rewrite IH by lia.
    replace (base + 1 + i + 1) with (base + S i + 1) by lia. reflexivity.
Qed.
Lemma returnRows_get : forall k base i, i < k ->
  nth_error (returnRows base k) i = Some (keepRow (base + i + 1) left).
Proof.
  intro k. induction k as [|k IH]; intros base [|i] hi; try lia.
  - cbn [returnRows nth_error]. replace (base + 0 + 1) with (base + 1) by lia. reflexivity.
  - cbn [returnRows nth_error]. rewrite IH by lia.
    replace (base + 1 + i + 1) with (base + S i + 1) by lia. reflexivity.
Qed.
Lemma write_instr : forall w i, i < length w -> forall a,
  instruction (emitter w) (4 + i) a = move (4 + i + 1) (ofBool (nth i w false)) right.
Proof.
  intros w i hi a. unfold instruction, emitter. cbn [program].
  rewrite <- app_assoc, nth_error_app2 by (cbn [setupRows length]; lia).
  cbn [setupRows length]. replace (4 + i - 4) with i by lia.
  rewrite nth_error_app1 by (rewrite writeRows_length; exact hi).
  rewrite writeRows_get by exact hi. destruct a; reflexivity.
Qed.
Lemma return_instr : forall w i, i < length w -> forall a,
  instruction (emitter w) (4 + length w + i) a =
    move (4 + length w + i + 1) a left.
Proof.
  intros w i hi a. unfold instruction, emitter. cbn [program].
  rewrite nth_error_app2 by (rewrite length_app, writeRows_length; cbn [setupRows length]; lia).
  rewrite length_app, writeRows_length. cbn [setupRows length].
  replace (4 + length w + i - (4 + length w)) with i by lia.
  rewrite returnRows_get by exact hi. destruct a; reflexivity.
Qed.

Definition cfg (q : nat) (l r : list Symbol) : Config :=
  match r with
  | [] => {| state := q; tapeLeft := l; tapeHead := blank; tapeRight := [] |}
  | a :: r => {| state := q; tapeLeft := l; tapeHead := a; tapeRight := r |}
  end.
Lemma blanks_snoc : forall n, blanks (n + 1) = blanks n ++ [blank].
Proof.
  intro n. unfold blanks. rewrite repeat_app. simpl. reflexivity.
Qed.
Lemma erase_reaches : forall out w l,
  Reaches (emitter out) (cfg 1 l (map ofBool w)) (length w)
    (cfg 1 (blanks (length w) ++ l) []).
Proof.
  intros out w. induction w as [|b w IH]; intro l.
  - apply reaches_refl.
  - assert (hs : step (emitter out) (cfg 1 l (map ofBool (b :: w))) =
      inr (cfg 1 (blank :: l) (map ofBool w))).
    { destruct b, w; reflexivity. }
    simpl length. replace (S (length w)) with (length w + 1) by lia.
    rewrite blanks_snoc, <- app_assoc. simpl app.
    replace (length w + 1) with (S (length w)) by lia.
    eapply reaches_next; [exact hs|]. apply IH.
Qed.
Definition revCfg (q : nat) (r l : list Symbol) : Config :=
  match l with
  | [] => {| state := q; tapeLeft := []; tapeHead := blank; tapeRight := r |}
  | a :: l => {| state := q; tapeLeft := l; tapeHead := a; tapeRight := r |}
  end.
Lemma return_origin : forall out n r,
  Reaches (emitter out) (revCfg 2 r (blanks n ++ [separator])) (n + 1)
    {| state := 3; tapeLeft := []; tapeHead := separator; tapeRight := blanks n ++ r |}.
Proof.
  intros out n. induction n as [|n IH]; intro r.
  - simpl. eapply reaches_next; [reflexivity|apply reaches_refl].
  - assert (hs : step (emitter out) (revCfg 2 r (blanks (S n) ++ [separator])) =
      inr (revCfg 2 (blank :: r) (blanks n ++ [separator]))).
    { destruct n; reflexivity. }
    replace (S n + 1) with (S (n + 1)) by lia.
    replace (blanks (S n) ++ r) with (blanks n ++ blank :: r).
    + eapply reaches_next; [exact hs|apply IH].
    + replace (S n) with (n + 1) by lia. rewrite blanks_snoc, <- app_assoc. reflexivity.
Qed.

(** Each written bit and each move restoring the head is a table instruction. *)
Theorem write_block : forall w m base,
  (forall i, i < length w -> forall a,
    instruction m (base + i) a = move (base + i + 1) (ofBool (nth i w false)) right) ->
  forall l padding,
  Reaches m {| state := base; tapeLeft := l; tapeHead := blank; tapeRight := blanks padding |}
    (length w)
    {| state := base + length w; tapeLeft := rev (map ofBool w) ++ l;
       tapeHead := blank; tapeRight := blanks (padding - length w) |}.
Proof.
  intro w. induction w as [|b w IH]; intros m base h l padding.
  - cbn [length map rev app]. rewrite Nat.add_0_r, Nat.sub_0_r. apply reaches_refl.
  - assert (hs : step m
      {| state := base; tapeLeft := l; tapeHead := blank; tapeRight := blanks padding |} =
      inr {| state := base + 1; tapeLeft := ofBool b :: l;
             tapeHead := blank; tapeRight := blanks (padding - 1) |}).
    { unfold step. cbn [state tapeHead].
      pose proof (h 0 ltac:(simpl; lia) blank) as h0.
      cbn [nth] in h0. rewrite Nat.add_0_r in h0. rewrite h0.
      destruct padding; cbn [blanks repeat moveHead tapeLeft tapeRight Nat.sub];
        try rewrite Nat.sub_0_r; reflexivity. }
    assert (ht : forall i, i < length w -> forall a,
      instruction m (base + 1 + i) a = move (base + 1 + i + 1) (ofBool (nth i w false)) right).
    { intros i hi a. pose proof (h (S i) ltac:(simpl; lia) a) as hh.
      cbn [nth] in hh. replace (base + S i) with (base + 1 + i) in hh by lia. exact hh. }
    pose proof (IH m (base + 1) ht (ofBool b :: l) (padding - 1)) as hr.
    cbn [map rev length]. rewrite <- app_assoc. simpl app.
    replace (base + S (length w)) with (base + 1 + length w) by lia.
    replace (padding - S (length w)) with (padding - 1 - length w) by lia.
    eapply reaches_next; [exact hs|exact hr].
Qed.

Theorem return_block : forall l m base a r,
  (forall i, i < length l -> forall s,
    instruction m (base + i) s = move (base + i + 1) s left) ->
  exists d, Reaches m {| state := base; tapeLeft := l; tapeHead := a; tapeRight := r |}
      (length l) d /\ state d = base + length l /\ tapeLeft d = [] /\
      tapeHead d :: tapeRight d = rev l ++ a :: r.
Proof.
  intro l. induction l as [|b l IH]; intros m base a r h.
  - exists {| state := base; tapeLeft := []; tapeHead := a; tapeRight := r |}.
    split; [apply reaches_refl|]. simpl. auto.
  - assert (hs : step m
      {| state := base; tapeLeft := b :: l; tapeHead := a; tapeRight := r |} =
      inr {| state := base + 1; tapeLeft := l; tapeHead := b; tapeRight := a :: r |}).
    { unfold step. cbn [state tapeHead]. pose proof (h 0 ltac:(simpl; lia) a) as h0.
      rewrite Nat.add_0_r in h0. rewrite h0. reflexivity. }
    assert (ht : forall i, i < length l -> forall s,
      instruction m (base + 1 + i) s = move (base + 1 + i + 1) s left).
    { intros i hi s. pose proof (h (S i) ltac:(simpl; lia) s) as hh.
      replace (base + S i) with (base + 1 + i) in hh by lia. exact hh. }
    destruct (IH m (base + 1) b (a :: r) ht) as [d [hd [hq [hl hr]]]].
    exists d. split; [eapply reaches_next; eassumption|].
    split; [simpl; lia|]. split; [exact hl|].
    simpl. rewrite <- app_assoc. simpl app. exact hr.
Qed.

Lemma prepare : forall w x, exists n, n <= length x /\
  Reaches (emitter w) (initial x) (2 * n + 4)
    {| state := 4; tapeLeft := []; tapeHead := blank; tapeRight := blanks (n + 1) |}.
Proof.
  intros w x.
  assert (hstart : forall tail,
    Reaches (emitter w) (cfg 1 [separator] (map ofBool tail)) (2 * length tail + 3)
      {| state := 4; tapeLeft := []; tapeHead := blank; tapeRight := blanks (length tail + 1) |}).
  { intro tail. pose proof (erase_reaches w tail [separator]) as he.
    assert (hs : step (emitter w) (cfg 1 (blanks (length tail) ++ [separator]) []) =
      inr (revCfg 2 [blank] (blanks (length tail) ++ [separator]))).
    { destruct (length tail); reflexivity. }
    pose proof (return_origin w (length tail) [blank]) as hr.
    assert (hc : step (emitter w)
      {| state := 3; tapeLeft := []; tapeHead := separator; tapeRight := blanks (length tail) ++ [blank] |} =
      inr {| state := 4; tapeLeft := []; tapeHead := blank; tapeRight := blanks (length tail + 1) |}).
    { rewrite blanks_snoc. reflexivity. }
    pose proof (reaches_next _ _ _ _ _ hc (reaches_refl _ _)) as hclear.
    pose proof (reaches_trans _ _ _ _ _ _ hr hclear) as hreturn.
    pose proof (reaches_next _ _ _ _ _ hs hreturn) as hback.
    pose proof (reaches_trans _ _ _ _ _ _ he hback) as hh.
    replace (length tail + S (length tail + 1 + 1)) with (2 * length tail + 3) in hh by lia.
    exact hh. }
  destruct x as [|b tail].
  - exists 0. split; [simpl; lia|].
    replace (2 * 0 + 4) with (S (2 * length (@nil bool) + 3)) by (simpl; lia).
    eapply reaches_next with (c' := cfg 1 [separator] []); [reflexivity|exact (hstart [])].
  - exists (length tail). split; [simpl; lia|].
    replace (2 * length tail + 4) with (S (2 * length tail + 3)) by lia.
    eapply reaches_next with (c' := cfg 1 [separator] (map ofBool tail)); [|exact (hstart tail)].
    destruct b, tail; reflexivity.
Qed.

Theorem emitter_computes : forall w,
  Computes (emitter w) (fun _ => w) (emitterPolynomial w).
Proof.
  intros w x. destruct (prepare w x) as [n [hn hp]].
  pose proof (write_block w (emitter w) 4 (write_instr w) [] (n + 1)) as hw.
  rewrite app_nil_r in hw.
  assert (hreturn : forall i, i < length (rev (map ofBool w)) -> forall s,
    instruction (emitter w) (4 + length w + i) s = move (4 + length w + i + 1) s left).
  { intros i hi s. rewrite length_rev, length_map in hi. apply return_instr. exact hi. }
  destruct (return_block (rev (map ofBool w)) (emitter w) (4 + length w)
    blank (blanks (n + 1 - length w)) hreturn) as [d [hd [hq [hl hr]]]].
  rewrite length_rev, length_map in hd, hq. rewrite rev_involutive in hr.
  exists (2 * n + 4 + length w + length w), d.
  split.
  - unfold emitterPolynomial, evalPoly. cbn [coefficient degree Nat.pow]. nia.
  - split; [eapply reaches_trans; [eapply reaches_trans; eassumption|exact hd]|].
    split; [rewrite emitter_states; lia|]. split; [exact hl|].
    exists (n + 1 - length w + 1). rewrite hr, blanks_snoc.
    unfold blanks. rewrite repeat_cons, app_assoc. reflexivity.
Qed.

End ConstantEmitter.
