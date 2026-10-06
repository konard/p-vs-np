From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Idea41Core.
From proofs.experiments.issue567.rocq Require Import CircuitSyntax.
Import Complexity Machines Circuits.

(** A finite CircuitSAT verifier with universal correctness and cubic charged termination. *)
Definition candidate : Machine := {| program := [
    [halt false; move 81 zero right; move 0 one right; halt false]; (* syntax_header *)
    [halt false; move 2 zero right; move 1 one right; halt false]; (* advance_first *)
    [halt false; move 36 zero right; move 2 one right; halt false]; (* advance_second *)
    [move 1 one right; move 3 zero left; move 3 one left; halt false]; (* append_back_gate *)
    [halt false; move 4 zero left; move 4 one left; move 3 separator left]; (* append_back_sep *)
    [move 4 zero left; move 5 zero right; move 5 one right; halt false]; (* append_false_end *)
    [halt false; move 6 zero right; move 6 one right; move 5 separator right]; (* append_false_sep *)
    [move 4 one left; move 7 zero right; move 7 one right; halt false]; (* append_true_end *)
    [halt false; move 8 zero right; move 8 one right; move 7 separator right]; (* append_true_sep *)
    [move 26 blank right; move 9 zero left; move 9 one left; move 9 separator left]; (* count_back_left *)
    [halt false; move 10 zero left; move 10 one left; move 9 separator left]; (* count_back_sep *)
    [move 16 blank left; halt false; halt false; halt false]; (* count_cert_empty *)
    [move 15 zero right; move 12 zero right; move 12 one right; move 15 one right]; (* count_cert_end *)
    [halt false; move 10 blank left; move 10 separator left; halt false]; (* count_cert_first *)
    [move 18 zero right; move 14 zero right; move 14 one right; move 18 one right]; (* count_cert_next *)
    [move 16 blank left; halt false; halt false; halt false]; (* count_check_end *)
    [halt false; move 16 zero left; move 16 one left; move 21 separator left]; (* count_finish_sep *)
    [halt false; move 22 zero right; move 24 separator right; halt false]; (* count_first *)
    [halt false; move 10 blank left; move 10 separator left; halt false]; (* count_mark_next *)
    [halt false; move 23 zero right; move 25 separator right; halt false]; (* count_next *)
    [halt false; move 36 zero right; halt false; move 20 one right]; (* count_restore *)
    [move 20 blank right; move 21 zero left; move 21 one left; move 21 separator left]; (* count_restore_left *)
    [halt false; move 22 zero right; move 22 one right; move 11 separator right]; (* count_seek_empty *)
    [halt false; move 23 zero right; move 23 one right; move 12 separator right]; (* count_seek_end *)
    [halt false; move 24 zero right; move 24 one right; move 13 separator right]; (* count_seek_first *)
    [halt false; move 25 zero right; move 25 one right; move 14 separator right]; (* count_seek_next *)
    [halt false; move 19 zero stay; move 19 one stay; move 26 separator right]; (* count_skip *)
    [halt false; halt false; halt false; move 28 separator right]; (* finish_boundary *)
    [halt false; move 28 zero right; move 29 one right; halt false]; (* finish_false *)
    [halt true; move 28 zero right; move 29 one right; halt false]; (* finish_true *)
    [move 32 blank right; move 30 zero left; move 30 one left; move 30 separator left]; (* first_restore_false_gate *)
    [halt false; move 31 zero left; move 31 one left; move 30 separator left]; (* first_restore_false_sep *)
    [halt false; move 51 zero right; halt false; move 32 one right]; (* first_restore_false_unary *)
    [move 35 blank right; move 33 zero left; move 33 one left; move 33 separator left]; (* first_restore_true_gate *)
    [halt false; move 34 zero left; move 34 one left; move 33 separator left]; (* first_restore_true_sep *)
    [halt false; move 62 zero right; halt false; move 35 one right]; (* first_restore_true_unary *)
    [halt false; move 27 zero right; move 41 blank right; halt false]; (* gate *)
    [move 46 blank right; move 37 zero left; move 37 one left; move 37 separator left]; (* lookup_first_back_gate *)
    [halt false; move 38 zero left; move 38 one left; move 37 separator left]; (* lookup_first_back_sep *)
    [move 43 zero right; move 39 zero right; move 39 one right; move 43 one right]; (* lookup_first_cursor_increment *)
    [move 31 zero left; move 40 zero right; move 40 one right; move 34 one left]; (* lookup_first_cursor_read *)
    [halt false; move 41 zero right; move 41 one right; move 42 separator right]; (* lookup_first_init *)
    [halt false; move 38 blank left; move 38 separator left; halt false]; (* lookup_first_mark_initial *)
    [halt false; move 38 blank left; move 38 separator left; halt false]; (* lookup_first_mark_next *)
    [halt false; move 44 zero right; move 44 one right; move 39 separator right]; (* lookup_first_seek_increment *)
    [halt false; move 45 zero right; move 45 one right; move 40 separator right]; (* lookup_first_seek_read *)
    [halt false; move 45 zero right; move 44 separator right; move 46 separator right]; (* lookup_first_unary *)
    [move 56 blank right; move 47 zero left; move 47 one left; move 47 separator left]; (* lookup_second_false_back_gate *)
    [halt false; move 48 zero left; move 48 one left; move 47 separator left]; (* lookup_second_false_back_sep *)
    [move 53 zero right; move 49 zero right; move 49 one right; move 53 one right]; (* lookup_second_false_cursor_increment *)
    [move 74 zero left; move 50 zero right; move 50 one right; move 74 one left]; (* lookup_second_false_cursor_read *)
    [halt false; move 51 zero right; move 51 one right; move 52 separator right]; (* lookup_second_false_init *)
    [halt false; move 48 blank left; move 48 separator left; halt false]; (* lookup_second_false_mark_initial *)
    [halt false; move 48 blank left; move 48 separator left; halt false]; (* lookup_second_false_mark_next *)
    [halt false; move 54 zero right; move 54 one right; move 49 separator right]; (* lookup_second_false_seek_increment *)
    [halt false; move 55 zero right; move 55 one right; move 50 separator right]; (* lookup_second_false_seek_read *)
    [halt false; move 57 zero right; move 56 one right; halt false]; (* lookup_second_false_skip_first *)
    [halt false; move 55 zero right; move 54 separator right; move 57 separator right]; (* lookup_second_false_unary *)
    [move 67 blank right; move 58 zero left; move 58 one left; move 58 separator left]; (* lookup_second_true_back_gate *)
    [halt false; move 59 zero left; move 59 one left; move 58 separator left]; (* lookup_second_true_back_sep *)
    [move 64 zero right; move 60 zero right; move 60 one right; move 64 one right]; (* lookup_second_true_cursor_increment *)
    [move 74 zero left; move 61 zero right; move 61 one right; move 70 one left]; (* lookup_second_true_cursor_read *)
    [halt false; move 62 zero right; move 62 one right; move 63 separator right]; (* lookup_second_true_init *)
    [halt false; move 59 blank left; move 59 separator left; halt false]; (* lookup_second_true_mark_initial *)
    [halt false; move 59 blank left; move 59 separator left; halt false]; (* lookup_second_true_mark_next *)
    [halt false; move 65 zero right; move 65 one right; move 60 separator right]; (* lookup_second_true_seek_increment *)
    [halt false; move 66 zero right; move 66 one right; move 61 separator right]; (* lookup_second_true_seek_read *)
    [halt false; move 68 zero right; move 67 one right; halt false]; (* lookup_second_true_skip_first *)
    [halt false; move 66 zero right; move 65 separator right; move 68 separator right]; (* lookup_second_true_unary *)
    [move 71 blank right; move 69 zero left; move 69 one left; move 69 separator left]; (* second_restore_false_gate *)
    [halt false; move 70 zero left; move 70 one left; move 69 separator left]; (* second_restore_false_sep *)
    [halt false; move 72 zero right; move 71 one right; halt false]; (* second_restore_false_skip_first *)
    [halt false; move 6 zero right; halt false; move 72 one right]; (* second_restore_false_unary *)
    [move 75 blank right; move 73 zero left; move 73 one left; move 73 separator left]; (* second_restore_true_gate *)
    [halt false; move 74 zero left; move 74 one left; move 73 separator left]; (* second_restore_true_sep *)
    [halt false; move 76 zero right; move 75 one right; halt false]; (* second_restore_true_skip_first *)
    [halt false; move 8 zero right; halt false; move 76 one right]; (* second_restore_true_unary *)
    [move 17 blank right; move 77 zero left; move 77 one left; halt false]; (* start_left *)
    [halt false; move 78 zero right; move 78 one right; halt false]; (* syntax_bad *)
    [halt false; move 78 zero right; move 78 one right; move 77 separator left]; (* syntax_done *)
    [halt false; move 82 zero right; move 80 one right; halt false]; (* syntax_first *)
    [halt false; move 79 zero right; move 80 one right; halt false]; (* syntax_marker *)
    [halt false; move 81 zero right; move 82 one right; halt false] (* syntax_second *)
] |}.

Example finite_table : length (program candidate) = 83.
Proof. reflexivity. Qed.

(* Universal tape lemmas for the exact generated table. *)

Definition cfg (q : nat) (L R : list Symbol) : Config :=
  match R with
  | [] => {| state := q; tapeLeft := L; tapeHead := blank; tapeRight := [] |}
  | a :: r => {| state := q; tapeLeft := L; tapeHead := a; tapeRight := r |}
  end.

Theorem stepR : forall q q' a w L R,
  instruction candidate q a = move q' w right ->
  step candidate (cfg q L (a :: R)) = inr (cfg q' (w :: L) R).
Proof.
  intros q q' a w L R h. unfold step. cbn [cfg state tapeHead]. rewrite h.
  destruct R; reflexivity.
Qed.

Theorem stepL : forall q q' a w l L R,
  instruction candidate q a = move q' w left ->
  step candidate (cfg q (l :: L) (a :: R)) = inr (cfg q' L (l :: w :: R)).
Proof.
  intros q q' a w l L R h. unfold step. cbn [cfg state tapeHead]. rewrite h. reflexivity.
Qed.

Theorem reaches_trans : forall c d e t u,
  Reaches candidate c t d -> Reaches candidate d u e -> Reaches candidate c (t + u) e.
Proof.
  intros c d e t u h h'. induction h.
  - exact h'.
  - replace (S t + u) with (S (t + u)) by lia.
    eapply reaches_next; [exact H | apply IHh; exact h'].
Qed.

Theorem R1 : forall q q' a w L R t E,
  instruction candidate q a = move q' w right ->
  Reaches candidate (cfg q' (w :: L) R) t E ->
  Reaches candidate (cfg q L (a :: R)) (S t) E.
Proof.
  intros q q' a w L R t E h hr.
  eapply reaches_next; [apply stepR; exact h | exact hr].
Qed.

Theorem L1 : forall q q' a w l L R t E,
  instruction candidate q a = move q' w left ->
  Reaches candidate (cfg q' L (l :: w :: R)) t E ->
  Reaches candidate (cfg q (l :: L) (a :: R)) (S t) E.
Proof.
  intros q q' a w l L R t E h hr.
  eapply reaches_next; [apply stepL; exact h | exact hr].
Qed.

Theorem walkR : forall q w L R,
  (forall a, In a w -> instruction candidate q a = move q a right) ->
  Reaches candidate (cfg q L (w ++ R)) (length w) (cfg q (rev w ++ L) R).
Proof.
  intros q w. induction w as [|a w ih]; intros L R h.
  - apply reaches_refl.
  - cbn [length app rev]. rewrite <- app_assoc. cbn [app].
    eapply R1; [apply h; now left |].
    apply ih. intros b hb. apply h. now right.
Qed.

Theorem walkL : forall q marker L w a R,
  (forall b, In b (a :: w) -> instruction candidate q b = move q b left) ->
  Reaches candidate (cfg q (w ++ marker :: L) (a :: R)) (S (length w))
    (cfg q L (marker :: rev w ++ a :: R)).
Proof.
  intros q marker L w. induction w as [|b w ih]; intros a R h.
  - eapply L1; [apply h; now left | apply reaches_refl].
  - cbn [app rev length]. rewrite <- app_assoc. cbn [app].
    eapply L1; [apply h; now left |].
    apply ih. intros c hc. apply h. now right.
Qed.

Theorem rewind : forall q q' marker a w L R,
  instruction candidate q a = move q' a left ->
  (forall b, In b w -> instruction candidate q' b = move q' b left) ->
  Reaches candidate (cfg q (w ++ marker :: L) (a :: R)) (S (length w))
    (cfg q' L (marker :: rev w ++ a :: R)).
Proof.
  intros q q' marker a w L R ha hw. destruct w as [|b w].
  - eapply L1; [exact ha | apply reaches_refl].
  - cbn [app rev length]. rewrite <- app_assoc. cbn [app].
    eapply L1; [exact ha |]. apply walkL. exact hw.
Qed.

Theorem bit_mem : forall a w,
  In a (map ofBool w) -> a = zero \/ a = one.
Proof.
  intros a w h. apply in_map_iff in h. destruct h as [b [<- _]].
  destruct b; [now right | now left].
Qed.

Definition cursor (b : bool) : Symbol := if b then separator else blank.

Theorem lookup_first_initial : forall w b v L,
  Reaches candidate (cfg 41 (blank :: L)
    (map ofBool w ++ separator :: map ofBool (b :: v)))
    (2 * length w + 4)
    (cfg 46 (blank :: L)
      (map ofBool w ++ separator :: cursor b :: map ofBool v)).
Proof.
  intros w b v L.
  assert (h1 : Reaches candidate
    (cfg 41 (blank :: L) (map ofBool w ++ separator :: map ofBool (b :: v)))
    (length w)
    (cfg 41 (rev (map ofBool w) ++ blank :: L)
      (separator :: map ofBool (b :: v)))).
  { rewrite <- (length_map ofBool w). apply walkR.
    intros a ha. destruct (bit_mem a w ha) as [-> | ->]; reflexivity. }
  assert (h4 : Reaches candidate
    (cfg 38 (rev (map ofBool w) ++ blank :: L)
      (separator :: cursor b :: map ofBool v))
    (length w + 1)
    (cfg 37 L
      (blank :: map ofBool w ++ separator :: cursor b :: map ofBool v))).
  { assert (hw : forall a, In a (rev (map ofBool w)) ->
      instruction candidate 37 a =
        move 37 a left).
    { intros a ha. apply in_rev in ha.
      destruct (bit_mem a w ha) as [-> | ->]; reflexivity. }
    pose proof (rewind 38 37
      blank separator (rev (map ofBool w)) L (cursor b :: map ofBool v) eq_refl hw) as h.
    rewrite length_rev, length_map, rev_involutive in h.
    replace (length w + 1) with (S (length w)) by lia. exact h. }
  assert (h5 : Reaches candidate
    (cfg 37 L
      (blank :: map ofBool w ++ separator :: cursor b :: map ofBool v)) 1
    (cfg 46 (blank :: L)
      (map ofBool w ++ separator :: cursor b :: map ofBool v))).
  { eapply R1; [reflexivity | apply reaches_refl]. }
  replace (2 * length w + 4) with
    (length w + S (S ((length w + 1) + 1))) by lia.
  eapply reaches_trans; [exact h1 |]. cbn [map].
  eapply R1; [reflexivity |].
  eapply (L1 42 38
    (ofBool b) (cursor b) separator); [destruct b; reflexivity |].
  eapply reaches_trans; [exact h4 | exact h5].
Qed.


(* Universal parser/rewind and terminal gate-loop invariants. *)

Definition syntaxIdx (q : CircuitSyntax.Phase) : nat :=
  match q with
  | CircuitSyntax.header => 0
  | CircuitSyntax.marker => 81
  | CircuitSyntax.firstWire => 80
  | CircuitSyntax.secondWire => 82
  | CircuitSyntax.done => 79
  | CircuitSyntax.bad => 78
  end.

Fixpoint phaseAfter (q : CircuitSyntax.Phase) (w : Word) : CircuitSyntax.Phase :=
  match w with [] => q | b :: w => phaseAfter (CircuitSyntax.next q b) w end.

Theorem phaseAfter_spec : forall q w,
  CircuitSyntax.syntaxFrom q w = CircuitSyntax.finished (phaseAfter q w).
Proof.
  intros q w. revert q. induction w as [|b w ih]; intro q; [reflexivity | apply ih].
Qed.

Theorem syntax_scan_reaches : forall q w L R,
  Reaches candidate (cfg (syntaxIdx q) L (map ofBool w ++ separator :: R)) (length w)
    (cfg (syntaxIdx (phaseAfter q w)) (rev (map ofBool w) ++ L) (separator :: R)).
Proof.
  intros q w. revert q. induction w as [|b w ih]; intros q L R.
  - apply reaches_refl.
  - cbn [map app rev length phaseAfter]. rewrite <- app_assoc. cbn [app].
    eapply (R1 (syntaxIdx q) (syntaxIdx (CircuitSyntax.next q b)) (ofBool b) (ofBool b));
      [destruct q, b; reflexivity | apply ih].
Qed.

Theorem paired_eq : forall w cert, pairedInput w cert =
  cfg (syntaxIdx CircuitSyntax.header) [] (map ofBool w ++ separator :: map ofBool cert).
Proof. intros w cert. destruct w; reflexivity. Qed.

Theorem malformed_reject : forall w cert,
  CircuitSyntax.circuitSyntax w = false ->
  Run candidate (pairedInput w cert) (length w + 1) false.
Proof.
  intros w cert hbad. rewrite paired_eq.
  eapply reaches_run; [apply syntax_scan_reaches |].
  apply run_halt. unfold step. cbn [cfg state tapeHead].
  unfold CircuitSyntax.circuitSyntax in hbad. rewrite phaseAfter_spec in hbad.
  destruct (phaseAfter CircuitSyntax.header w); try reflexivity. discriminate.
Qed.

Theorem walkLEnd : forall q w a R,
  (forall b, In b (a :: w) -> instruction candidate q b = move q b left) ->
  Reaches candidate (cfg q w (a :: R)) (S (length w))
    (cfg q [] (blank :: rev w ++ a :: R)).
Proof.
  intros q w. induction w as [|b w ih]; intros a R h.
  - eapply reaches_next; [|apply reaches_refl].
    unfold step. cbn [cfg state tapeHead]. rewrite (h a (or_introl eq_refl)). reflexivity.
  - cbn [rev length]. rewrite <- app_assoc. cbn [app].
    eapply L1; [apply h; now left |]. apply ih.
    intros c hc. apply h. now right.
Qed.

Theorem rewindEnd : forall q q' a w R,
  instruction candidate q a = move q' a left ->
  (forall b, In b w -> instruction candidate q' b = move q' b left) ->
  Reaches candidate (cfg q w (a :: R)) (S (length w))
    (cfg q' [] (blank :: rev w ++ a :: R)).
Proof.
  intros q q' a w R ha hw. destruct w as [|b w].
  - eapply reaches_next; [|apply reaches_refl].
    unfold step. cbn [cfg state tapeHead]. rewrite ha. reflexivity.
  - cbn [rev length]. rewrite <- app_assoc. cbn [app].
    eapply L1; [exact ha | apply walkLEnd; exact hw].
Qed.

Theorem valid_start : forall w cert,
  CircuitSyntax.circuitSyntax w = true ->
  Reaches candidate (pairedInput w cert) (2 * length w + 2)
    (cfg 17 [blank] (map ofBool w ++ separator :: map ofBool cert)).
Proof.
  intros w cert hvalid.
  assert (hf : phaseAfter CircuitSyntax.header w = CircuitSyntax.done).
  { unfold CircuitSyntax.circuitSyntax in hvalid. rewrite phaseAfter_spec in hvalid.
    destruct (phaseAfter CircuitSyntax.header w); try discriminate; reflexivity. }
  pose proof (syntax_scan_reaches CircuitSyntax.header w [] (map ofBool cert)) as h1.
  rewrite hf, app_nil_r in h1.
  assert (hw : forall a, In a (rev (map ofBool w)) ->
    instruction candidate 77 a = move 77 a left).
  { intros a ha. apply in_rev in ha.
    destruct (bit_mem a w ha) as [-> | ->]; reflexivity. }
  pose proof (rewindEnd (syntaxIdx CircuitSyntax.done) 77 separator
    (rev (map ofBool w)) (map ofBool cert) eq_refl hw) as h2.
  rewrite length_rev, length_map, rev_involutive in h2.
  assert (h3 : Reaches candidate (cfg 77 []
    (blank :: map ofBool w ++ separator :: map ofBool cert)) 1
    (cfg 17 [blank] (map ofBool w ++ separator :: map ofBool cert))).
  { eapply R1; [reflexivity | apply reaches_refl]. }
  rewrite paired_eq. replace (2 * length w + 2) with
    (length w + (S (length w) + 1)) by lia.
  eapply reaches_trans; [exact h1 |].
  eapply reaches_trans; [exact h2 | exact h3].
Qed.

Fixpoint lastFrom (b : bool) (w : Word) : bool :=
  match w with [] => b | a :: w => lastFrom a w end.

Theorem finish_run : forall (b : bool) (w : Word) (L : list Symbol),
  Run candidate (cfg (if b then 29 else 28) L (map ofBool w))
    (length w + 1) (lastFrom b w).
Proof.
  intros b w. revert b. induction w as [|a w ih]; intros b L.
  - apply run_halt. destruct b; reflexivity.
  - cbn [map length lastFrom]. rewrite Nat.add_1_r.
    eapply run_next; [apply (stepR (if b then 29 else 28)
      (if a then 29 else 28) (ofBool a) (ofBool a));
      destruct b, a; reflexivity |].
    replace (S (length w)) with (length w + 1) by lia. apply ih.
Qed.

Theorem lastFrom_eq_last : forall b w, lastFrom b w = last w b.
Proof.
  intros b w. revert b. induction w as [|a w ih]; intro b; [reflexivity |].
  destruct w as [|c w]; [reflexivity |]. apply ih.
Qed.

Theorem gate_empty_run : forall w L,
  Run candidate (cfg 36 L (zero :: separator :: map ofBool w))
    (length w + 3) (last w false).
Proof.
  intros w L.
  assert (h1 : Reaches candidate (cfg 36 L (zero :: separator :: map ofBool w)) 2
    (cfg 28 (separator :: zero :: L) (map ofBool w))).
  { eapply R1; [reflexivity |]. eapply R1; [reflexivity | apply reaches_refl]. }
  pose proof (finish_run false w (separator :: zero :: L)) as h2.
  rewrite lastFrom_eq_last in h2.
  replace (length w + 3) with (2 + (length w + 1)) by lia.
  eapply reaches_run; [exact h1 | exact h2].
Qed.



(* Exact certificate-matching shuttles on the generated instruction table. *)
Definition ones (n : nat) : list Symbol := repeat one n.
Definition marks (n : nat) : list Symbol := repeat separator n.

Ltac cells :=
  repeat rewrite map_app; repeat rewrite rev_app_distr;
  repeat rewrite rev_involutive; repeat rewrite rev_repeat;
  repeat rewrite length_app; repeat rewrite length_map;
  repeat rewrite length_rev; repeat rewrite length_map; repeat rewrite repeat_length;
  cbn [map rev app length]; repeat rewrite rev_repeat;
  repeat rewrite repeat_length; repeat rewrite <- app_assoc;
  cbn [app]; repeat rewrite Nat.add_1_r.
Ltac cells_in H :=
  repeat rewrite map_app in H; repeat rewrite rev_app_distr in H;
  repeat rewrite rev_involutive in H; repeat rewrite rev_repeat in H;
  repeat rewrite length_app in H; repeat rewrite length_map in H;
  repeat rewrite length_rev in H; repeat rewrite length_map in H;
  repeat rewrite repeat_length in H;
  cbn [map rev app length] in H; repeat rewrite rev_repeat in H;
  repeat rewrite repeat_length in H; repeat rewrite <- app_assoc in H;
  cbn [app] in H; repeat rewrite Nat.add_1_r in H.
Tactic Notation "cells" "in" ident(H) := cells_in H.

Lemma marks_mem : forall a n, In a (marks n) -> a = separator.
Proof. intros a n h. apply repeat_spec in h. exact h. Qed.

Lemma bitR : forall q w L R,
  (forall b, instruction candidate q (ofBool b) = move q (ofBool b) right) ->
  Reaches candidate (cfg q L (map ofBool w ++ R)) (length w)
    (cfg q (rev (map ofBool w) ++ L) R).
Proof.
  intros q w L R h. rewrite <- (length_map ofBool w). apply walkR.
  intros a ha. apply in_map_iff in ha. destruct ha as [b [hb _]]. subst a. apply h.
Qed.

Lemma bits_back : forall q q' marker w L a R,
  instruction candidate q a = move q' a left ->
  (forall b, instruction candidate q' (ofBool b) = move q' (ofBool b) left) ->
  Reaches candidate (cfg q (rev (map ofBool w) ++ marker :: L) (a :: R))
    (length w + 1) (cfg q' L (marker :: map ofBool w ++ a :: R)).
Proof.
  intros q q' marker w L a R ha hw.
  pose proof (rewind q q' marker a (rev (map ofBool w)) L R ha) as h.
  rewrite length_rev, length_map, rev_involutive in h.
  replace (length w + 1) with (S (length w)) by lia. apply h.
  intros b hb. apply in_rev in hb. apply in_map_iff in hb.
  destruct hb as [c [hc _]]. subst b. apply hw.
Qed.

Theorem count_return_sep : forall p r R, r <> [] ->
  Reaches candidate (cfg 10
    (rev (map ofBool r) ++ marks p ++ [blank]) (separator :: R))
    (length r + 2 * p + 3)
    (cfg 19 (marks p ++ [blank]) (map ofBool r ++ separator :: R)).
Proof.
  intros p r R hne.
  assert (hw : forall a, In a (rev (map ofBool r) ++ marks p) ->
      instruction candidate 9 a = move 9 a left).
  { intros a ha. apply in_app_or in ha. destruct ha as [ha | ha].
    - apply in_rev in ha. destruct (bit_mem a r ha) as [-> | ->]; reflexivity.
    - rewrite (marks_mem a p ha). reflexivity. }
  pose proof (rewind 10 9 blank separator
    (rev (map ofBool r) ++ marks p) [] R eq_refl hw) as h1.
  assert (h2 : Reaches candidate
    (cfg 26 [blank] (marks p ++ map ofBool r ++ separator :: R)) p
    (cfg 26 (marks p ++ [blank]) (map ofBool r ++ separator :: R))).
  { assert (hw' : forall a, In a (marks p) ->
      instruction candidate 26 a = move 26 a right).
    { intros a ha. rewrite (marks_mem a p ha). reflexivity. }
    pose proof (walkR 26 (marks p) [blank]
      (map ofBool r ++ separator :: R) hw') as h.
    unfold marks in h. rewrite repeat_length, rev_repeat in h. exact h. }
  assert (h3 : Reaches candidate
    (cfg 26 (marks p ++ [blank]) (map ofBool r ++ separator :: R)) 1
    (cfg 19 (marks p ++ [blank]) (map ofBool r ++ separator :: R))).
  { destruct r as [|b r]; [contradiction |].
    eapply reaches_next; [|apply reaches_refl]. destruct b; reflexivity. }
  unfold marks in *. cells in h1.
  replace (length r + 2 * p + 3) with (S (length r + p) + S (p + 1)) by lia.
  eapply reaches_trans; [exact h1 |].
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h2 | exact h3].
Qed.

Theorem count_return : forall p r u b R, r <> [] ->
  Reaches candidate (cfg 10
    (rev (map ofBool u) ++ separator :: rev (map ofBool r) ++ marks p ++ [blank])
    (ofBool b :: R)) (length u + length r + 2 * p + 4)
    (cfg 19 (marks p ++ [blank])
      (map ofBool r ++ separator :: map ofBool (u ++ [b]) ++ R)).
Proof.
  intros p r u b R hne.
  assert (hb : instruction candidate 10 (ofBool b) =
    move 10 (ofBool b) left) by (destruct b; reflexivity).
  pose proof (bits_back 10 10 separator u
    (rev (map ofBool r) ++ marks p ++ [blank]) (ofBool b) R hb
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (count_return_sep p r (map ofBool (u ++ [b]) ++ R) hne) as h2.
  cells in h1. cells in h2. cells.
  replace (length u + length r + 2 * p + 4) with
    (S (length u) + (length r + 2 * p + 3)) by lia.
  eapply reaches_trans; [exact h1 | exact h2].
Qed.

Lemma ones_shift : forall p L, one :: repeat one p ++ L = repeat one p ++ one :: L.
Proof. induction p; intro L; cbn [repeat app]; [reflexivity |]. f_equal. apply IHp. Qed.

Lemma restore_marks : forall p L R,
  Reaches candidate (cfg 20 L (marks p ++ R)) p
    (cfg 20 (ones p ++ L) R).
Proof.
  induction p as [|p ih]; intros L R; [apply reaches_refl |].
  unfold marks, ones in *. cbn [repeat app].
  rewrite ones_shift.
  eapply R1; [reflexivity | apply ih].
Qed.

Theorem count_finish : forall q p r cert,
  instruction candidate q blank = move 16 blank left ->
  Reaches candidate (cfg q (rev (map ofBool cert) ++ separator ::
    rev (map ofBool r) ++ zero :: marks p ++ [blank]) [])
    (length cert + length r + 2 * p + 5)
    (cfg 36 (zero :: ones p ++ [blank])
      (map ofBool r ++ separator :: map ofBool cert ++ [blank])).
Proof.
  intros q p r cert hq.
  pose proof (bits_back q 16 separator cert
    (rev (map ofBool r) ++ zero :: marks p ++ [blank]) blank [] hq
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  assert (hw : forall a, In a (rev (map ofBool r) ++ zero :: marks p) ->
    instruction candidate 21 a = move 21 a left).
  { intros a ha. apply in_app_or in ha. destruct ha as [ha | [ha | ha]].
    - apply in_rev in ha. destruct (bit_mem a r ha) as [-> | ->]; reflexivity.
    - subst a. reflexivity.
    - rewrite (marks_mem a p ha). reflexivity. }
  pose proof (rewind 16 21 blank separator
    (rev (map ofBool r) ++ zero :: marks p) [] (map ofBool cert ++ [blank]) eq_refl hw) as h2.
  pose proof (restore_marks p [blank]
    (zero :: map ofBool r ++ separator :: map ofBool cert ++ [blank])) as h3.
  unfold marks in *. cells in h1. cells in h2. cells in h3. cells.
  replace (length cert + length r + 2 * p + 5) with
    (S (length cert) + (S (length r + S p) + S (p + 1))) by lia.
  eapply reaches_trans; [exact h1 |].
  eapply reaches_trans; [exact h2 |].
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h3 |].
  eapply R1; [reflexivity | apply reaches_refl].
Qed.

Theorem count_advance : forall p n w u b c v,
  Reaches candidate (cfg 19 (marks p ++ [blank])
    (ones (S n) ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool (c :: v)))
    (2 * (n + length w + length u + p) + 12)
    (cfg 19 (marks (S p) ++ [blank])
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool (u ++ [b]) ++ cursor c :: map ofBool v)).
Proof.
  intros p n w u b c v. set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR 25 r (marks (S p) ++ [blank])
    (separator :: map ofBool u ++ cursor b :: map ofBool (c :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (bitR 14 u
    (separator :: rev (map ofBool r) ++ marks (S p) ++ [blank])
    (cursor b :: map ofBool (c :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h2.
  pose proof (count_return (S p) r u b (cursor c :: map ofBool v)) as h3.
  assert (hne : r <> []). { unfold r. intro h. apply (f_equal (@length bool)) in h. cells in h. lia. }
  specialize (h3 hne). cells in h1. cells in h2. cells in h3.
  change (ones (S n)) with (one :: ones n).
  rewrite hr in h1, h2, h3. cells in h1. cells in h2. cells in h3. cells.
  replace (2 * (n + length w + length u + p) + 12) with
    (S (length r + S (length u + S (S (length u + length r + 2 * S p + 4))))) by
    (unfold r; cells; lia).
  eapply R1; [reflexivity |].
  eapply reaches_trans; [exact h1 |]. eapply R1; [reflexivity |].
  eapply reaches_trans; [exact h2 |].
  eapply (R1 14 18 (cursor b) (ofBool b));
    [destruct b; reflexivity |].
  eapply (L1 18 10 (ofBool c) (cursor c) (ofBool b));
    [destruct c; reflexivity | exact h3].
Qed.

Theorem count_short : forall p n w u b,
  Run candidate (cfg 19 (marks p ++ [blank])
    (ones (S n) ++ zero :: map ofBool w ++ separator :: map ofBool u ++ [cursor b]))
    (n + length w + length u + 5) false.
Proof.
  intros p n w u b. set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR 25 r (marks (S p) ++ [blank])
    (separator :: map ofBool u ++ [cursor b])
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (bitR 14 u
    (separator :: rev (map ofBool r) ++ marks (S p) ++ [blank]) [cursor b]
    ltac:(intro bit; destruct bit; reflexivity)) as h2.
  cells in h1. cells in h2. change (ones (S n)) with (one :: ones n).
  rewrite hr in h1, h2. cells in h1. cells in h2. cells.
  replace (n + length w + length u + 5) with
    (S (length r + S (length u + S 1))) by (unfold r; cells; lia).
  eapply run_next; [apply stepR; reflexivity |].
  eapply reaches_run; [exact h1 |]. eapply run_next; [apply stepR; reflexivity |].
  eapply reaches_run; [exact h2 |].
  eapply run_next;
    [eapply (stepR 14 18 (cursor b) (ofBool b));
      destruct b; reflexivity |].
  apply run_halt. reflexivity.
Qed.

Theorem count_end_success : forall p w u b,
  Reaches candidate (cfg 19 (marks p ++ [blank])
    (zero :: map ofBool w ++ separator :: map ofBool u ++ [cursor b]))
    (2 * (length w + length u + p) + 9)
    (cfg 36 (zero :: ones p ++ [blank])
      (map ofBool w ++ separator :: map ofBool (u ++ [b]) ++ [blank])).
Proof.
  intros p w u b.
  pose proof (bitR 23 w (zero :: marks p ++ [blank])
    (separator :: map ofBool u ++ [cursor b])
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (bitR 12 u
    (separator :: rev (map ofBool w) ++ zero :: marks p ++ [blank]) [cursor b]
    ltac:(intro bit; destruct bit; reflexivity)) as h2.
  pose proof (count_finish 15 p w (u ++ [b]) eq_refl) as h3.
  cells in h1. cells in h2. cells in h3. cells.
  replace (2 * (length w + length u + p) + 9) with
    (S (length w + S (length u + S (length (u ++ [b]) + length w + 2 * p + 5)))) by
    (cells; lia).
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h1 |].
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h2 |].
  eapply (R1 12 15 (cursor b) (ofBool b));
    [destruct b; reflexivity | cells; exact h3].
Qed.

Theorem count_end_long : forall p w u b c v,
  Run candidate (cfg 19 (marks p ++ [blank])
    (zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool (c :: v)))
    (length w + length u + 4) false.
Proof.
  intros p w u b c v.
  pose proof (bitR 23 w (zero :: marks p ++ [blank])
    (separator :: map ofBool u ++ cursor b :: map ofBool (c :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (bitR 12 u
    (separator :: rev (map ofBool w) ++ zero :: marks p ++ [blank])
    (cursor b :: map ofBool (c :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h2.
  cells in h1. cells in h2. cells.
  replace (length w + length u + 4) with (S (length w + S (length u + S 1))) by lia.
  eapply run_next; [apply stepR; reflexivity |].
  eapply reaches_run; [exact h1 |]. eapply run_next; [apply stepR; reflexivity |].
  eapply reaches_run; [exact h2 |].
  eapply run_next;
    [eapply (stepR 12 15 (cursor b) (ofBool b));
      destruct b; reflexivity |].
  apply run_halt. destruct c; reflexivity.
Qed.

Theorem count_tail_success : forall n p K w u b v,
  length v = n -> p + n + length w + length u + length v + 4 <= K ->
  exists t, t <= 32 * (n + 1) * K /\
    Reaches candidate (cfg 19 (marks p ++ [blank])
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool v)) t
      (cfg 36 (zero :: ones (p + n) ++ [blank])
        (map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ [blank])).
Proof.
  induction n as [|n ih]; intros p K w u b v hv hK.
  - destruct v; [|discriminate].
    exists (2 * (length w + length u + p) + 9). split; [cbn in hK; nia |].
    pose proof (count_end_success p w u b) as h. cells in h. cells.
    replace (p + 0) with p by lia. exact h.
  - destruct v as [|c v]; [discriminate |].
    assert (hv' : length v = n) by (cbn in hv; lia).
    assert (hK' : S p + n + length w + length (u ++ [b]) + length v + 4 <= K)
      by (rewrite length_app; cbn; cbn in hK; lia).
    destruct (ih (S p) K w (u ++ [b]) c v hv' hK') as [t [ht hr]].
    pose proof (count_advance p n w u b c v) as hs.
    assert (hc : 2 * (n + length w + length u + p) + 12 <= 32 * K) by (cbn in hK; lia).
    exists (2 * (n + length w + length u + p) + 12 + t). split; [nia |].
    cells in hr. cells in hs. cells.
    replace (p + S n) with (S p + n) by lia.
    eapply reaches_trans; [exact hs | exact hr].
Qed.

Theorem count_tail_reject : forall n p K w u b v,
  length v <> n -> p + n + length w + length u + length v + 4 <= K ->
  exists t, t <= 32 * (n + 1) * K /\
    Run candidate (cfg 19 (marks p ++ [blank])
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool v)) t false.
Proof.
  induction n as [|n ih]; intros p K w u b v hv hK.
  - destruct v as [|c v]; [contradiction |].
    exists (length w + length u + 4). split; [cbn in hK; nia |].
    exact (count_end_long p w u b c v).
  - destruct v as [|c v].
    + exists (n + length w + length u + 5). split; [cbn in hK; nia |].
      exact (count_short p n w u b).
    + assert (hv' : length v <> n) by (cbn in hv; lia).
      assert (hK' : S p + n + length w + length (u ++ [b]) + length v + 4 <= K)
        by (rewrite length_app; cbn; cbn in hK; lia).
      destruct (ih (S p) K w (u ++ [b]) c v hv' hK') as [t [ht hr]].
      pose proof (count_advance p n w u b c v) as hs.
      assert (hc : 2 * (n + length w + length u + p) + 12 <= 32 * K) by (cbn in hK; lia).
      exists (2 * (n + length w + length u + p) + 12 + t). split; [nia |].
      cells in hr. cells in hs. cells. eapply reaches_run; [exact hs | exact hr].
Qed.

Theorem count_first_start : forall n w b v,
  Reaches candidate (cfg 17 [blank]
    (ones (S n) ++ zero :: map ofBool w ++ separator :: map ofBool (b :: v)))
    (2 * (n + length w) + 10)
    (cfg 19 (marks 1 ++ [blank])
      (ones n ++ zero :: map ofBool w ++ separator :: cursor b :: map ofBool v)).
Proof.
  intros n w b v. set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR 24 r [separator; blank]
    (separator :: map ofBool (b :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  assert (hne : r <> []). { unfold r. intro h. apply (f_equal (@length bool)) in h. cells in h. lia. }
  pose proof (count_return_sep 1 r (cursor b :: map ofBool v) hne) as h2.
  change (ones (S n)) with (one :: ones n).
  rewrite hr in h1, h2. cells in h1. cells in h2. cells.
  replace (2 * (n + length w) + 10) with (S (length r + S (S (length r + 2 * 1 + 3)))) by
    (unfold r; cells; lia).
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h1 |].
  eapply R1; [reflexivity |].
  eapply (L1 13 10 (ofBool b) (cursor b) separator);
    [destruct b; reflexivity | exact h2].
Qed.

Theorem count_first_short : forall n w,
  Run candidate (cfg 17 [blank]
    (ones (S n) ++ zero :: map ofBool w ++ [separator])) (n + length w + 4) false.
Proof.
  intros n w. set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR 24 r [separator; blank] [separator]
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  change (ones (S n)) with (one :: ones n).
  rewrite hr in h1. cells in h1. cells.
  replace (n + length w + 4) with (S (length r + S 1)) by (unfold r; cells; lia).
  eapply run_next; [apply stepR; reflexivity |]. eapply reaches_run; [exact h1 |].
  eapply run_next; [apply stepR; reflexivity |]. apply run_halt. reflexivity.
Qed.

Theorem count_zero_success : forall w,
  Reaches candidate (cfg 17 [blank] (zero :: map ofBool w ++ [separator]))
    (2 * length w + 7) (cfg 36 [zero; blank] (map ofBool w ++ [separator; blank])).
Proof.
  intro w.
  pose proof (bitR 22 w [zero; blank] [separator]
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  pose proof (count_finish 11 0 w [] eq_refl) as h2.
  unfold marks, ones in h2. cbn [repeat] in h2. cells in h1. cells in h2. cells.
  replace (0 + length w + 2 * 0 + 5) with (length w + 5) in h2 by lia.
  replace (2 * length w + 7) with (S (length w + S (length w + 5))) by lia.
  eapply R1; [reflexivity |]. eapply reaches_trans; [exact h1 |].
  eapply R1; [reflexivity | exact h2].
Qed.

Theorem count_zero_long : forall w b v,
  Run candidate (cfg 17 [blank]
    (zero :: map ofBool w ++ separator :: map ofBool (b :: v))) (length w + 3) false.
Proof.
  intros w b v.
  pose proof (bitR 22 w [zero; blank] (separator :: map ofBool (b :: v))
    ltac:(intro bit; destruct bit; reflexivity)) as h1.
  cells in h1. cells.
  replace (length w + 3) with (S (length w + S 1)) by lia.
  eapply run_next; [apply stepR; reflexivity |]. eapply reaches_run; [exact h1 |].
  eapply run_next; [apply stepR; reflexivity |]. apply run_halt. destruct b; reflexivity.
Qed.

(* Every matching certificate reaches the gate phase with its bits and header
   restored. The bound counts the shuttles' actual charged instructions. *)
Theorem count_success : forall n w cert, length cert = n ->
  exists t, t <= 64 * (n + 1) * (n + length w + length cert + 4) /\
    Reaches candidate (cfg 17 [blank]
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool cert)) t
      (cfg 36 (zero :: ones n ++ [blank])
        (map ofBool w ++ separator :: map ofBool cert ++ [blank])).
Proof.
  intros n w cert hc. destruct n as [|n].
  - destruct cert; [|discriminate].
    exists (2 * length w + 7). split; [cbn; lia |]. exact (count_zero_success w).
  - destruct cert as [|b v]; [discriminate |].
    set (K := S n + length w + length (b :: v) + 4).
    assert (hv : length v = n) by (cbn in hc; lia).
    assert (hK : 1 + n + length w + length (@nil bool) + length v + 4 <= K)
      by (unfold K; cbn; lia).
    destruct (count_tail_success n 1 K w [] b v hv hK) as [t [ht hr]].
    pose proof (count_first_start n w b v) as hs.
    assert (hc' : 2 * (n + length w) + 10 <= 32 * K) by (unfold K; cbn; lia).
    exists (2 * (n + length w) + 10 + t). split; [fold K; nia |].
    cells in hs. cells in hr. cells. replace (1 + n) with (S n) in hr by lia.
    eapply reaches_trans; [exact hs | exact hr].
Qed.

(* Both too-short and too-long certificates halt before gate evaluation. *)
Theorem count_reject : forall n w cert, length cert <> n ->
  exists t, t <= 64 * (n + 1) * (n + length w + length cert + 4) /\
    Run candidate (cfg 17 [blank]
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool cert)) t false.
Proof.
  intros n w cert hc. destruct n as [|n].
  - destruct cert as [|b v]; [contradiction |].
    exists (length w + 3). split; [cbn; lia |]. exact (count_zero_long w b v).
  - destruct cert as [|b v].
    + exists (n + length w + 4). split; [cbn; nia |]. exact (count_first_short n w).
    + set (K := S n + length w + length (b :: v) + 4).
      assert (hv : length v <> n) by (cbn in hc; lia).
      assert (hK : 1 + n + length w + length (@nil bool) + length v + 4 <= K)
        by (unfold K; cbn; lia).
      destruct (count_tail_reject n 1 K w [] b v hv hK) as [t [ht hr]].
      pose proof (count_first_start n w b v) as hs.
      assert (hc' : 2 * (n + length w) + 10 <= 32 * K) by (unfold K; cbn; lia).
      exists (2 * (n + length w) + 10 + t). split; [fold K; nia |].
      cells in hs. cells in hr. cells. eapply reaches_run; [exact hs | exact hr].
Qed.



(* Unary wire lookup on the charged finite evaluator table. *)
Inductive LookupKind := first | secondFalse | secondTrue.
Definition lookupPrefix (k : LookupKind) (j : nat) : list Symbol :=
  match k with first => [] | _ => ones j ++ [zero] end.
Definition lookupInit (k : LookupKind) : nat :=
  match k with
  | first => 41
  | secondFalse => 51
  | secondTrue => 62
  end.
Definition lookupBackSep (k : LookupKind) : nat :=
  match k with
  | first => 38
  | secondFalse => 48
  | secondTrue => 59
  end.
Definition lookupBackGate (k : LookupKind) : nat :=
  match k with
  | first => 37
  | secondFalse => 47
  | secondTrue => 58
  end.
Definition lookupUnary (k : LookupKind) : nat :=
  match k with
  | first => 46
  | secondFalse => 57
  | secondTrue => 68
  end.
Definition lookupSeekIncrement (k : LookupKind) : nat :=
  match k with
  | first => 44
  | secondFalse => 54
  | secondTrue => 65
  end.
Definition lookupCursorIncrement (k : LookupKind) : nat :=
  match k with
  | first => 39
  | secondFalse => 49
  | secondTrue => 60
  end.
Definition lookupMarkNext (k : LookupKind) : nat :=
  match k with
  | first => 43
  | secondFalse => 53
  | secondTrue => 64
  end.
Definition lookupSkipFirst (k : LookupKind) : nat :=
  match k with
  | first => 46
  | secondFalse => 56
  | secondTrue => 67
  end.
Definition lookupSeekRead (k : LookupKind) : nat :=
  match k with
  | first => 45
  | secondFalse => 55
  | secondTrue => 66
  end.
Definition lookupCursorRead (k : LookupKind) : nat :=
  match k with
  | first => 40
  | secondFalse => 50
  | secondTrue => 61
  end.
Definition lookupMarkInitial (k : LookupKind) : nat :=
  match k with
  | first => 42
  | secondFalse => 52
  | secondTrue => 63
  end.
Definition lookupReadValue (k : LookupKind) (b : bool) : bool :=
  match k with first => b | secondFalse => true | secondTrue => negb b end.
Definition restoreSep (k : LookupKind) (b : bool) : nat :=
  match k, lookupReadValue k b with
  | first, false => 31
  | first, true => 34
  | _, false => 70
  | _, true => 74
  end.
Definition restoreGate (k : LookupKind) (b : bool) : nat :=
  match k, lookupReadValue k b with
  | first, false => 30
  | first, true => 33
  | _, false => 69
  | _, true => 73
  end.
Definition restoreUnary (k : LookupKind) (b : bool) : nat :=
  match k, lookupReadValue k b with
  | first, false => 32
  | first, true => 35
  | _, false => 72
  | _, true => 76
  end.
Definition restoreSkipFirst (k : LookupKind) (b : bool) : nat :=
  match k, lookupReadValue k b with
  | first, _ => restoreUnary k b
  | _, false => 71
  | _, true => 75
  end.
Definition lookupExit (k : LookupKind) (b : bool) : nat :=
  match k, lookupReadValue k b with
  | first, false => 51
  | first, true => 62
  | _, false => 6
  | _, true => 8
  end.

Ltac charge t :=
  match goal with
  | |- Reaches _ _ ?n _ => replace n with t by lia
  | |- Run _ _ ?n _ => replace n with t by lia
  end.

Lemma ones_mem : forall a n, In a (ones n) -> a = one.
Proof. intros a n h. apply repeat_spec in h. exact h. Qed.

Lemma lookup_prefix_mem : forall k j a,
  In a (lookupPrefix k j) -> a = zero \/ a = one.
Proof.
  intros k j a h. destruct k; cbn [lookupPrefix] in h; [contradiction | |];
    apply in_app_or in h; destruct h as [h | [h | h]];
    try contradiction; [right; eapply ones_mem; exact h | now left |
                       right; eapply ones_mem; exact h | now left].
Qed.

Theorem lookup_resume : forall k j p L R,
  Reaches candidate (cfg (lookupBackGate k) L
    (blank :: lookupPrefix k j ++ marks p ++ R))
    (1 + length (lookupPrefix k j) + p)
    (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L) R).
Proof.
  intros k j p L R.
  assert (hm : Reaches candidate
    (cfg (lookupUnary k) (rev (lookupPrefix k j) ++ blank :: L) (marks p ++ R)) p
    (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L) R)).
  { pose proof (walkR (lookupUnary k) (marks p)
      (rev (lookupPrefix k j) ++ blank :: L) R) as h.
    unfold marks in h. rewrite repeat_length, rev_repeat in h. apply h.
    intros a ha. apply repeat_spec in ha. subst a. destruct k; reflexivity. }
  destruct k.
  - cbn [lookupPrefix length app rev] in *. charge (S p).
    eapply R1; [reflexivity | exact hm].
  - assert (hp : Reaches candidate
      (cfg 56 (blank :: L) (ones j ++ zero :: marks p ++ R)) j
      (cfg 56 (ones j ++ blank :: L) (zero :: marks p ++ R))).
    { pose proof (walkR 56 (ones j) (blank :: L)
        (zero :: marks p ++ R)) as h. unfold ones in h.
      rewrite repeat_length, rev_repeat in h. apply h.
      intros a ha. apply repeat_spec in ha. subst a. reflexivity. }
    unfold lookupPrefix, ones in *. cells in hm. cells in hp. cells.
    pose proof (R1 56 (lookupUnary secondFalse) zero zero _ _ _ _ eq_refl hm) as hz.
    pose proof (reaches_trans _ _ _ _ _ hp hz) as h.
    pose proof (R1 (lookupBackGate secondFalse) 56 blank blank _ _ _ _ eq_refl h) as h4.
    charge (S (j + S p)).
    exact h4.
  - assert (hp : Reaches candidate
      (cfg 67 (blank :: L) (ones j ++ zero :: marks p ++ R)) j
      (cfg 67 (ones j ++ blank :: L) (zero :: marks p ++ R))).
    { pose proof (walkR 67 (ones j) (blank :: L)
        (zero :: marks p ++ R)) as h. unfold ones in h.
      rewrite repeat_length, rev_repeat in h. apply h.
      intros a ha. apply repeat_spec in ha. subst a. reflexivity. }
    unfold lookupPrefix, ones in *. cells in hm. cells in hp. cells.
    pose proof (R1 67 (lookupUnary secondTrue) zero zero _ _ _ _ eq_refl hm) as hz.
    pose proof (reaches_trans _ _ _ _ _ hp hz) as h.
    pose proof (R1 (lookupBackGate secondTrue) 67 blank blank _ _ _ _ eq_refl h) as h4.
    charge (S (j + S p)).
    exact h4.
Qed.

Theorem lookup_return : forall k j p r u b L R,
  Reaches candidate (cfg (lookupBackSep k)
    (rev (map ofBool u) ++ separator :: rev (map ofBool r) ++
      marks p ++ rev (lookupPrefix k j) ++ blank :: L) (ofBool b :: R))
    (length u + length r + 2 * p + 2 * length (lookupPrefix k j) + 3)
    (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
      (map ofBool r ++ separator :: map ofBool (u ++ [b]) ++ R)).
Proof.
  intros k j p r u b L R.
  pose proof (bits_back (lookupBackSep k) (lookupBackSep k) separator u
    (rev (map ofBool r) ++ marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (ofBool b) R ltac:(destruct k, b; reflexivity)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  assert (hw : forall a, In a (rev (map ofBool r) ++ marks p ++ rev (lookupPrefix k j)) ->
    instruction candidate (lookupBackGate k) a = move (lookupBackGate k) a left).
  { intros a ha. repeat rewrite <- app_assoc in ha.
    apply in_app_or in ha. destruct ha as [ha | ha].
    - apply in_rev in ha. destruct (bit_mem a r ha) as [-> | ->]; destruct k; reflexivity.
    - apply in_app_or in ha. destruct ha as [ha | ha].
      + rewrite (marks_mem a p ha). destruct k; reflexivity.
      + apply in_rev in ha. destruct (lookup_prefix_mem k j a ha) as [-> | ->]; destruct k; reflexivity. }
  pose proof (rewind (lookupBackSep k) (lookupBackGate k) blank separator
    (rev (map ofBool r) ++ marks p ++ rev (lookupPrefix k j)) L
    (map ofBool (u ++ [b]) ++ R) ltac:(destruct k; reflexivity) hw) as h2.
  pose proof (lookup_resume k j p L (map ofBool r ++ separator :: map ofBool (u ++ [b]) ++ R)) as h3.
  unfold marks in *. cells in h1. cells in h2. cells in h3. cells.
  pose proof (reaches_trans _ _ _ _ _ h1 (reaches_trans _ _ _ _ _ h2 h3)) as h.
  let ty := type of h in match ty with Reaches _ _ ?t _ => charge t end. exact h.
Qed.

Theorem lookup_advance : forall k j p n w u b c v L T,
  Reaches candidate (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (ones (S n) ++ zero :: map ofBool w ++ separator :: map ofBool u ++
      cursor b :: map ofBool (c :: v) ++ T))
    (2 * (n + length w + length u + p + length (lookupPrefix k j)) + 11)
    (cfg (lookupUnary k) (marks (S p) ++ rev (lookupPrefix k j) ++ blank :: L)
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool (u ++ [b]) ++ cursor c :: map ofBool v ++ T)).
Proof.
  intros k j p n w u b c v L T.
  set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR (lookupSeekIncrement k) r
    (marks (S p) ++ rev (lookupPrefix k j) ++ blank :: L)
    (separator :: map ofBool u ++ cursor b :: map ofBool (c :: v) ++ T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  pose proof (bitR (lookupCursorIncrement k) u
    (separator :: rev (map ofBool r) ++ marks (S p) ++ rev (lookupPrefix k j) ++ blank :: L)
    (cursor b :: map ofBool (c :: v) ++ T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h2.
  pose proof (lookup_return k j (S p) r u b L (cursor c :: map ofBool v ++ T)) as h3.
  unfold marks in *. cells in h1. cells in h2. cells in h3. cells.
  assert (hlen : length r = n + S (length w)) by
    (unfold r; rewrite length_app, repeat_length; cbn [length]; lia).
  charge (S (length r + S (length u + S (S (length u + length r +
      2 * S p + 2 * length (lookupPrefix k j) + 3))))).
  unfold ones in hr |- *. cbn [repeat app].
  rewrite hr in h1, h2, h3. cells in h1. cells in h2. cells in h3. cells. cbn [repeat] in *.
  eapply (R1 (lookupUnary k) (lookupSeekIncrement k) one separator); [destruct k; reflexivity |].
  eapply reaches_trans; [exact h1 |]. eapply (R1 (lookupSeekIncrement k) (lookupCursorIncrement k) separator separator); [destruct k; reflexivity |].
  eapply reaches_trans; [exact h2 |].
  eapply (R1 (lookupCursorIncrement k) (lookupMarkNext k) (cursor b) (ofBool b));
    [destruct k, b; reflexivity |].
  eapply (L1 (lookupMarkNext k) (lookupBackSep k) (ofBool c) (cursor c) (ofBool b));
    [destruct k, c; reflexivity | exact h3].
Qed.

Theorem lookup_short : forall k j p n w u b L T,
  (T = [] \/ T = [blank]) ->
  Run candidate (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (ones (S n) ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: T))
    (n + length w + length u + 5) false.
Proof.
  intros k j p n w u b L T hT.
  set (r := repeat true n ++ false :: w).
  assert (hr : map ofBool r = ones n ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  pose proof (bitR (lookupSeekIncrement k) r
    (marks (S p) ++ rev (lookupPrefix k j) ++ blank :: L)
    (separator :: map ofBool u ++ cursor b :: T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  pose proof (bitR (lookupCursorIncrement k) u
    (separator :: rev (map ofBool r) ++ marks (S p) ++ rev (lookupPrefix k j) ++ blank :: L)
    (cursor b :: T) ltac:(intro bit; destruct k, bit; reflexivity)) as h2.
  unfold marks in *. cells in h1. cells in h2. cells.
  replace (n + length w + length u + 5) with (S (length r + S (length u + S 1))) by
    (unfold r; rewrite length_app, repeat_length; cbn [length]; lia).
  unfold ones in hr |- *. cbn [repeat app].
  rewrite hr in h1, h2. cells in h1. cells in h2. cells. cbn [repeat] in *.
  eapply run_next; [apply (stepR (lookupUnary k) (lookupSeekIncrement k) one separator); destruct k; reflexivity |].
  eapply reaches_run; [exact h1 |].
  eapply run_next; [apply (stepR (lookupSeekIncrement k) (lookupCursorIncrement k) separator separator); destruct k; reflexivity |].
  eapply reaches_run; [exact h2 |].
  eapply run_next; [apply (stepR (lookupCursorIncrement k) (lookupMarkNext k) (cursor b) (ofBool b));
    destruct k, b; reflexivity |].
  apply run_halt. destruct hT as [-> | ->]; destruct k; reflexivity.
Qed.

Theorem rewindWrite : forall q q' marker a write w L R,
  instruction candidate q a = move q' write left ->
  (forall b, In b w -> instruction candidate q' b = move q' b left) ->
  Reaches candidate (cfg q (w ++ marker :: L) (a :: R)) (S (length w))
    (cfg q' L (marker :: rev w ++ write :: R)).
Proof.
  intros q q' marker a write w L R ha hw. destruct w as [|b w].
  - eapply L1; [exact ha | apply reaches_refl].
  - cbn [app rev length]. rewrite <- app_assoc. cbn [app].
    eapply L1; [exact ha |]. apply walkL. exact hw.
Qed.

Theorem restore_ticks : forall k b p L R,
  Reaches candidate (cfg (restoreUnary k b) L (marks p ++ R)) p
    (cfg (restoreUnary k b) (ones p ++ L) R).
Proof.
  intros k b p. induction p as [|p ih]; intros L R; [apply reaches_refl |].
  unfold marks, ones in *. cbn [repeat app]. rewrite ones_shift.
  eapply (R1 (restoreUnary k b) (restoreUnary k b) separator one);
    [destruct k, b; reflexivity | apply ih].
Qed.

Theorem restore_resume : forall k b j p L R,
  Reaches candidate (cfg (restoreGate k b) L (blank :: lookupPrefix k j ++ marks p ++ R))
    (1 + length (lookupPrefix k j) + p)
    (cfg (restoreUnary k b) (ones p ++ rev (lookupPrefix k j) ++ blank :: L) R).
Proof.
  intros k b j p L R.
  pose proof (restore_ticks k b p (rev (lookupPrefix k j) ++ blank :: L) R) as hm.
  destruct k.
  - cbn [lookupPrefix length app rev] in *. charge (S p).
    eapply (R1 (restoreGate first b) (restoreUnary first b) blank blank);
      [destruct b; reflexivity | exact hm].
  - assert (hp : Reaches candidate
      (cfg (restoreSkipFirst secondFalse b) (blank :: L) (ones j ++ zero :: marks p ++ R)) j
      (cfg (restoreSkipFirst secondFalse b) (ones j ++ blank :: L) (zero :: marks p ++ R))).
    { pose proof (walkR (restoreSkipFirst secondFalse b) (ones j) (blank :: L)
        (zero :: marks p ++ R)) as h. unfold ones in h.
      rewrite repeat_length, rev_repeat in h. apply h.
      intros a ha. apply repeat_spec in ha. subst a. destruct b; reflexivity. }
    unfold lookupPrefix, ones in *. cells in hm. cells in hp. cells.
    pose proof (R1 (restoreSkipFirst secondFalse b) (restoreUnary secondFalse b) zero zero
      _ _ _ _ ltac:(destruct b; reflexivity) hm) as hz.
    pose proof (reaches_trans _ _ _ _ _ hp hz) as h.
    pose proof (R1 (restoreGate secondFalse b) (restoreSkipFirst secondFalse b) blank blank
      _ _ _ _ ltac:(destruct b; reflexivity) h) as h4.
    charge (S (j + S p)). exact h4.
  - assert (hp : Reaches candidate
      (cfg (restoreSkipFirst secondTrue b) (blank :: L) (ones j ++ zero :: marks p ++ R)) j
      (cfg (restoreSkipFirst secondTrue b) (ones j ++ blank :: L) (zero :: marks p ++ R))).
    { pose proof (walkR (restoreSkipFirst secondTrue b) (ones j) (blank :: L)
        (zero :: marks p ++ R)) as h. unfold ones in h.
      rewrite repeat_length, rev_repeat in h. apply h.
      intros a ha. apply repeat_spec in ha. subst a. destruct b; reflexivity. }
    unfold lookupPrefix, ones in *. cells in hm. cells in hp. cells.
    pose proof (R1 (restoreSkipFirst secondTrue b) (restoreUnary secondTrue b) zero zero
      _ _ _ _ ltac:(destruct b; reflexivity) hm) as hz.
    pose proof (reaches_trans _ _ _ _ _ hp hz) as h.
    pose proof (R1 (restoreGate secondTrue b) (restoreSkipFirst secondTrue b) blank blank
      _ _ _ _ ltac:(destruct b; reflexivity) h) as h4.
    charge (S (j + S p)). exact h4.
Qed.

Theorem lookup_read : forall k j p w u b v L T,
  Reaches candidate (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool v ++ T))
    (2 * (length w + length u + p + length (lookupPrefix k j)) + 7)
    (cfg (lookupExit k b) (zero :: ones p ++ rev (lookupPrefix k j) ++ blank :: L)
      (map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ T)).
Proof.
  intros k j p w u b v L T.
  pose proof (bitR (lookupSeekRead k) w
    (zero :: marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (separator :: map ofBool u ++ cursor b :: map ofBool v ++ T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  pose proof (bitR (lookupCursorRead k) u
    (separator :: rev (map ofBool w) ++ zero :: marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (cursor b :: map ofBool v ++ T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h2.
  assert (hw3 : forall a, In a (rev (map ofBool u)) ->
    instruction candidate (restoreSep k b) a = move (restoreSep k b) a left).
  { intros a ha. apply in_rev in ha. destruct (bit_mem a u ha) as [-> | ->]; destruct k, b; reflexivity. }
  pose proof (rewindWrite (lookupCursorRead k) (restoreSep k b) separator (cursor b) (ofBool b)
    (rev (map ofBool u))
    (rev (map ofBool w) ++ zero :: marks p ++ rev (lookupPrefix k j) ++ blank :: L)
    (map ofBool v ++ T) ltac:(destruct k, b; reflexivity) hw3) as h3.
  assert (hw4 : forall a,
    In a (rev (map ofBool w) ++ zero :: marks p ++ rev (lookupPrefix k j)) ->
    instruction candidate (restoreGate k b) a = move (restoreGate k b) a left).
  { intros a ha. repeat rewrite <- app_assoc in ha.
    apply in_app_or in ha. destruct ha as [ha | [ha | ha]].
    - apply in_rev in ha. destruct (bit_mem a w ha) as [-> | ->]; destruct k, b; reflexivity.
    - subst a. destruct k, b; reflexivity.
    - apply in_app_or in ha. destruct ha as [ha | ha].
      + rewrite (marks_mem a p ha). destruct k, b; reflexivity.
      + apply in_rev in ha. destruct (lookup_prefix_mem k j a ha) as [-> | ->]; destruct k, b; reflexivity. }
  pose proof (rewind (restoreSep k b) (restoreGate k b) blank separator
    (rev (map ofBool w) ++ zero :: marks p ++ rev (lookupPrefix k j)) L
    (map ofBool (u ++ b :: v) ++ T) ltac:(destruct k, b; reflexivity) hw4) as h4.
  pose proof (restore_resume k b j p L
    (zero :: map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ T)) as h5.
  assert (h6 : Reaches candidate (cfg (restoreUnary k b)
    (ones p ++ rev (lookupPrefix k j) ++ blank :: L)
    (zero :: map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ T)) 1
    (cfg (lookupExit k b) (zero :: ones p ++ rev (lookupPrefix k j) ++ blank :: L)
      (map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ T))).
  { eapply (R1 (restoreUnary k b) (lookupExit k b) zero zero);
      [destruct k, b; reflexivity | apply reaches_refl]. }
  unfold marks in *. cells in h1. cells in h2. cells in h3. cells in h4. cells in h4. cells in h5. cells in h6. cells.
  pose proof (reaches_trans _ _ _ _ _ h3 (reaches_trans _ _ _ _ _ h4
    (reaches_trans _ _ _ _ _ h5 h6))) as h.
  pose proof (reaches_trans _ _ _ _ _ h2 h) as h'.
  pose proof (R1 (lookupSeekRead k) (lookupCursorRead k) separator separator _ _ _ _
    ltac:(destruct k; reflexivity) h') as h''.
  pose proof (reaches_trans _ _ _ _ _ h1 h'') as h'''.
  pose proof (R1 (lookupUnary k) (lookupSeekRead k) zero zero _ _ _ _
    ltac:(destruct k; reflexivity) h''') as h''''.
  charge (S (length w + S (length u + (S (length u) +
      (S (length w + S (p + length (lookupPrefix k j))) +
        (1 + length (lookupPrefix k j) + p + 1)))))).
  exact h''''.
Qed.

Theorem lookup_initial : forall k j w b v L T,
  Reaches candidate (cfg (lookupInit k) (rev (lookupPrefix k j) ++ blank :: L)
    (map ofBool w ++ separator :: map ofBool (b :: v) ++ T))
    (2 * length w + 2 * length (lookupPrefix k j) + 4)
    (cfg (lookupUnary k) (rev (lookupPrefix k j) ++ blank :: L)
      (map ofBool w ++ separator :: cursor b :: map ofBool v ++ T)).
Proof.
  intros k j w b v L T.
  pose proof (bitR (lookupInit k) w (rev (lookupPrefix k j) ++ blank :: L)
    (separator :: map ofBool (b :: v) ++ T)
    ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  assert (hw : forall a, In a (rev (map ofBool w) ++ rev (lookupPrefix k j)) ->
    instruction candidate (lookupBackGate k) a = move (lookupBackGate k) a left).
  { intros a ha. apply in_app_or in ha. destruct ha as [ha | ha]; apply in_rev in ha.
    - destruct (bit_mem a w ha) as [-> | ->]; destruct k; reflexivity.
    - destruct (lookup_prefix_mem k j a ha) as [-> | ->]; destruct k; reflexivity. }
  pose proof (rewind (lookupBackSep k) (lookupBackGate k) blank separator
    (rev (map ofBool w) ++ rev (lookupPrefix k j)) L
    (cursor b :: map ofBool v ++ T) ltac:(destruct k; reflexivity) hw) as h2.
  pose proof (lookup_resume k j 0 L (map ofBool w ++ separator :: cursor b :: map ofBool v ++ T)) as h3.
  unfold marks in *. cells in h1. cells in h2. cells in h3. cells.
  pose proof (reaches_trans _ _ _ _ _ h2 h3) as h.
  pose proof (L1 (lookupMarkInitial k) (lookupBackSep k) (ofBool b) (cursor b) separator
    _ _ _ _ ltac:(destruct k, b; reflexivity) h) as h4.
  pose proof (R1 (lookupInit k) (lookupMarkInitial k) separator separator _ _ _ _
    ltac:(destruct k; reflexivity) h4) as h5.
  pose proof (reaches_trans _ _ _ _ _ h1 h5) as h6.
  charge (length w + S (S (S (length w + length (lookupPrefix k j)) +
      (1 + length (lookupPrefix k j) + 0)))).
  exact h6.
Qed.

Theorem lookup_empty : forall k j w L T,
  (T = [] \/ T = [blank]) ->
  Run candidate (cfg (lookupInit k) (rev (lookupPrefix k j) ++ blank :: L)
    (map ofBool w ++ separator :: T)) (length w + 2) false.
Proof.
  intros k j w L T hT.
  pose proof (bitR (lookupInit k) w (rev (lookupPrefix k j) ++ blank :: L)
    (separator :: T) ltac:(intro bit; destruct k, bit; reflexivity)) as h1.
  charge (length w + S 1).
  eapply reaches_run; [exact h1 |].
  eapply run_next; [apply (stepR (lookupInit k) (lookupMarkInitial k) separator separator); destruct k; reflexivity |].
  apply run_halt. destruct hT as [-> | ->]; destruct k; reflexivity.
Qed.

(** Used unary ticks and the wire cursor advance together for every index. *)
Theorem lookup_tail_success : forall n k j p K w u b v L T,
  n < length (b :: v) ->
  p + n + length w + length u + length v + length (lookupPrefix k j) + 4 <= K ->
  exists t, t <= 32 * (n + 1) * K /\
    Reaches candidate (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool v ++ T)) t
      (cfg (lookupExit k (Circuits.wire (b :: v) n))
        (zero :: ones (p + n) ++ rev (lookupPrefix k j) ++ blank :: L)
        (map ofBool w ++ separator :: map ofBool (u ++ b :: v) ++ T)).
Proof.
  induction n as [|n ih]; intros k j p K w u b v L T hn hK.
  - exists (2 * (length w + length u + p + length (lookupPrefix k j)) + 7).
    split; [nia |]. cbn [ones repeat app Circuits.wire nth]. rewrite Nat.add_0_r.
    apply lookup_read.
  - destruct v as [|c v]; [cbn [length] in hn; lia |].
    assert (hn' : n < length (c :: v)) by (cbn [length] in *; lia).
    assert (hK' : S p + n + length w + length (u ++ [b]) + length v +
      length (lookupPrefix k j) + 4 <= K) by (rewrite length_app; cbn [length] in *; lia).
    destruct (ih k j (S p) K w (u ++ [b]) c v L T hn' hK') as [t [ht hr]].
    pose proof (lookup_advance k j p n w u b c v L T) as hs.
    assert (hb : 2 * (n + length w + length u + p + length (lookupPrefix k j)) + 11 <= 32 * K)
      by (cbn [length] in hK; lia).
    exists (2 * (n + length w + length u + p + length (lookupPrefix k j)) + 11 + t).
    split; [nia |].
    unfold Circuits.wire in *. cbn [nth] in *. cells in hs. cells in hr. cells.
    replace (p + S n) with (S p + n) by lia.
    exact (reaches_trans _ _ _ _ _ hs hr).
Qed.

(** Unavailable wires reject for both representations of the terminal blank. *)
Theorem lookup_tail_reject : forall n k j p K w u b v L T,
  length (b :: v) <= n -> (T = [] \/ T = [blank]) ->
  p + n + length w + length u + length v + length (lookupPrefix k j) + 4 <= K ->
  exists t, t <= 32 * (n + 1) * K /\
    Run candidate (cfg (lookupUnary k) (marks p ++ rev (lookupPrefix k j) ++ blank :: L)
      (ones n ++ zero :: map ofBool w ++ separator :: map ofBool u ++ cursor b :: map ofBool v ++ T)) t false.
Proof.
  induction n as [|n ih]; intros k j p K w u b v L T hn hT hK.
  - cbn [length] in hn. lia.
  - destruct v as [|c v].
    + exists (n + length w + length u + 5). split; [cbn [length] in hK; nia |].
      cbn [map app]. apply lookup_short. exact hT.
    + assert (hn' : length (c :: v) <= n) by (cbn [length] in *; lia).
      assert (hK' : S p + n + length w + length (u ++ [b]) + length v +
        length (lookupPrefix k j) + 4 <= K) by (rewrite length_app; cbn [length] in *; lia).
      destruct (ih k j (S p) K w (u ++ [b]) c v L T hn' hT hK') as [t [ht hr]].
      pose proof (lookup_advance k j p n w u b c v L T) as hs.
      assert (hb : 2 * (n + length w + length u + p + length (lookupPrefix k j)) + 11 <= 32 * K)
        by (cbn [length] in hK; lia).
      exists (2 * (n + length w + length u + p + length (lookupPrefix k j)) + 11 + t).
      split; [nia |]. cells in hs. cells in hr. cells.
      exact (reaches_run _ _ _ _ _ _ hs hr).
Qed.

Theorem lookup_success : forall k j i K w v L T,
  i < length v ->
  i + length w + length v + length (lookupPrefix k j) + 4 <= K ->
  exists t, t <= 64 * (i + 1) * K /\
    Reaches candidate (cfg (lookupInit k) (rev (lookupPrefix k j) ++ blank :: L)
      (ones i ++ zero :: map ofBool w ++ separator :: map ofBool v ++ T)) t
      (cfg (lookupExit k (Circuits.wire v i)) (zero :: ones i ++ rev (lookupPrefix k j) ++ blank :: L)
        (map ofBool w ++ separator :: map ofBool v ++ T)).
Proof.
  intros k j i K w v L T hi hK. destruct v as [|b v]; [cbn [length] in hi; lia |].
  set (r := repeat true i ++ false :: w).
  assert (he : map ofBool r = ones i ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  assert (hlen : length r = i + S (length w)) by
    (unfold r; rewrite length_app, repeat_length; cbn [length]; lia).
  pose proof (lookup_initial k j r b v L T) as hinit. rewrite he in hinit. cells in hinit.
  assert (hK' : 0 + i + length w + length (@nil bool) + length v +
    length (lookupPrefix k j) + 4 <= K) by (cbn [length] in *; lia).
  destruct (lookup_tail_success i k j 0 K w [] b v L T hi hK') as [t [ht hr]].
  assert (hb : 2 * length r + 2 * length (lookupPrefix k j) + 4 <= 32 * K) by
    (cbn [length] in hK; lia).
  exists (2 * length r + 2 * length (lookupPrefix k j) + 4 + t).
  split; [nia |]. unfold marks in hr. cbn [repeat map app Nat.add] in hr. cells in hr. cells.
  exact (reaches_trans _ _ _ _ _ hinit hr).
Qed.

Theorem lookup_reject : forall k j i K w v L T,
  length v <= i -> (T = [] \/ T = [blank]) ->
  i + length w + length v + length (lookupPrefix k j) + 4 <= K ->
  exists t, t <= 64 * (i + 1) * K /\
    Run candidate (cfg (lookupInit k) (rev (lookupPrefix k j) ++ blank :: L)
      (ones i ++ zero :: map ofBool w ++ separator :: map ofBool v ++ T)) t false.
Proof.
  intros k j i K w v L T hi hT hK.
  set (r := repeat true i ++ false :: w).
  assert (he : map ofBool r = ones i ++ zero :: map ofBool w).
  { unfold r, ones. rewrite map_app, map_repeat. reflexivity. }
  assert (hlen : length r = i + S (length w)) by
    (unfold r; rewrite length_app, repeat_length; cbn [length]; lia).
  destruct v as [|b v].
  - exists (length r + 2). split; [cbn [length] in hK; nia |].
    pose proof (lookup_empty k j r L T hT) as h. rewrite he in h. cells in h. cells. exact h.
  - pose proof (lookup_initial k j r b v L T) as hinit. rewrite he in hinit. cells in hinit.
    assert (hK' : 0 + i + length w + length (@nil bool) + length v +
      length (lookupPrefix k j) + 4 <= K) by (cbn [length] in *; lia).
    destruct (lookup_tail_reject i k j 0 K w [] b v L T hi hT hK') as [t [ht hr]].
    assert (hb : 2 * length r + 2 * length (lookupPrefix k j) + 4 <= 32 * K) by
      (cbn [length] in hK; lia).
    exists (2 * length r + 2 * length (lookupPrefix k j) + 4 + t).
    split; [nia |]. unfold marks in hr. cbn [repeat map app Nat.add] in hr. cells in hr. cells.
    exact (reaches_run _ _ _ _ _ _ hinit hr).
Qed.



From Stdlib Require Import Bool.

(** Append one NAND result and restore both unary indices and the gate marker. *)
Definition appendSep (b : bool) : nat := if b then 8 else 6.
Definition appendEnd (b : bool) : nat := if b then 7 else 5.

Theorem append_gate : forall b i j w v L T,
  (T = [] \/ T = [blank]) ->
  Reaches candidate (cfg (appendSep b) (zero :: ones j ++ zero :: ones i ++ blank :: L)
    (map ofBool w ++ separator :: map ofBool v ++ T))
    (2 * length w + 2 * length v + 2 * i + 2 * j + 8)
    (cfg 36 (zero :: ones j ++ zero :: ones i ++ one :: L)
      (map ofBool w ++ separator :: map ofBool (v ++ [b]))).
Proof.
  intros b i j w v L T hT.
  pose proof (bitR (appendSep b) w (zero :: ones j ++ zero :: ones i ++ blank :: L)
    (separator :: map ofBool v ++ T) ltac:(intro a; destruct b, a; reflexivity)) as h1.
  pose proof (bitR (appendEnd b) v
    (separator :: rev (map ofBool w) ++ zero :: ones j ++ zero :: ones i ++ blank :: L)
    T ltac:(intro a; destruct b, a; reflexivity)) as h2.
  pose proof (rewindWrite (appendEnd b) 4 separator blank (ofBool b)
    (rev (map ofBool v))
    (rev (map ofBool w) ++ zero :: ones j ++ zero :: ones i ++ blank :: L) []
    ltac:(destruct b; reflexivity)
    ltac:(intros a ha; apply in_rev in ha; destruct (bit_mem a v ha) as [-> | ->]; reflexivity)) as h3.
  assert (hw : forall a, In a (rev (map ofBool w) ++ zero :: ones j ++ zero :: ones i) ->
    instruction candidate 3 a = move 3 a left).
  { intros a ha. repeat rewrite <- app_assoc in ha.
    apply in_app_or in ha. destruct ha as [ha | [ha | ha]].
    - apply in_rev in ha. destruct (bit_mem a w ha) as [-> | ->]; reflexivity.
    - subst a. reflexivity.
    - apply in_app_or in ha. destruct ha as [ha | [ha | ha]].
      + rewrite (ones_mem a j ha). reflexivity.
      + subst a. reflexivity.
      + rewrite (ones_mem a i ha). reflexivity. }
  pose proof (rewind 4 3 blank separator
    (rev (map ofBool w) ++ zero :: ones j ++ zero :: ones i) L
    (map ofBool (v ++ [b])) eq_refl hw) as h4.
  pose proof (walkR 2 (ones j) (zero :: ones i ++ one :: L)
    (zero :: map ofBool w ++ separator :: map ofBool (v ++ [b]))
    ltac:(intros a ha; rewrite (ones_mem a j ha); reflexivity)) as h5.
  assert (h6 : Reaches candidate (cfg 2
      (ones j ++ zero :: ones i ++ one :: L)
      (zero :: map ofBool w ++ separator :: map ofBool (v ++ [b]))) 1
      (cfg 36 (zero :: ones j ++ zero :: ones i ++ one :: L)
        (map ofBool w ++ separator :: map ofBool (v ++ [b])))).
  { eapply R1; [reflexivity | apply reaches_refl]. }
  pose proof (walkR 1 (ones i) (one :: L)
    (zero :: ones j ++ zero :: map ofBool w ++ separator :: map ofBool (v ++ [b]))
    ltac:(intros a ha; rewrite (ones_mem a i ha); reflexivity)) as h7.
  unfold ones in *. cells in h1. cells in h2. cells in h3. cells in h4. cells in h4.
  cells in h5. cells in h6. cells in h7. cells.
  pose proof (reaches_trans _ _ _ _ _ h5 h6) as h8.
  pose proof (R1 1 2 zero zero _ _ _ _ eq_refl h8) as h9.
  pose proof (reaches_trans _ _ _ _ _ h7 h9) as h10.
  pose proof (R1 3 1 blank one _ _ _ _ eq_refl h10) as h11.
  pose proof (reaches_trans _ _ _ _ _ h4 h11) as h12.
  pose proof (reaches_trans _ _ _ _ _ h3 h12) as h13.
  assert (h14 : Reaches candidate (cfg (appendEnd b)
      (rev (map ofBool v) ++ separator :: rev (map ofBool w) ++
        zero :: repeat one j ++ zero :: repeat one i ++ blank :: L) T)
      (S (length v) + (S (length w + S (j + S i)) + S (i + S (j + 1))))
      (cfg 36 (zero :: repeat one j ++ zero :: repeat one i ++ one :: L)
        (map ofBool w ++ separator :: map ofBool v ++ [ofBool b]))).
  { destruct hT as [-> | ->]; exact h13. }
  pose proof (reaches_trans _ _ _ _ _ h2 h14) as h15.
  pose proof (R1 (appendSep b) (appendEnd b) separator separator _ _ _ _
    ltac:(destruct b; reflexivity) h15) as h16.
  pose proof (reaches_trans _ _ _ _ _ h1 h16) as h.
  let ty := type of h in match ty with Reaches _ _ ?t _ => charge t end. exact h.
Qed.


Theorem finish_padded : forall (w : list bool) (b : bool) L T,
  (T = [] \/ T = [blank]) ->
  Run candidate (cfg (if b then 29 else 28) L
    (map ofBool w ++ T)) (length w + 1) (lastFrom b w).
Proof.
  induction w as [|a w ih]; intros b L T hT.
  - apply run_halt. destruct hT as [-> | ->]; destruct b; reflexivity.
  - cbn [map app length lastFrom]. rewrite Nat.add_1_r.
    eapply run_next; [apply (stepR (if b then 29 else 28)
      (if a then 29 else 28) (ofBool a) (ofBool a));
      destruct b, a; reflexivity |]. pose proof (ih a (ofBool a :: L) T hT) as h. rewrite Nat.add_1_r in h. exact h.
Qed.

Theorem gate_empty_padded : forall v L T,
  (T = [] \/ T = [blank]) ->
  Run candidate (cfg 36 L (zero :: separator :: map ofBool v ++ T))
    (length v + 3) (last v false).
Proof.
  intros v L T hT. pose proof (finish_padded v false (separator :: zero :: L) T hT) as h.
  rewrite lastFrom_eq_last in h. cells in h. cells.
  charge (S (S (S (length v)))).
  eapply run_next; [apply (stepR 36 27 zero zero); reflexivity |].
  eapply run_next; [apply (stepR 27 28 separator separator); reflexivity |]. exact h.
Qed.

Definition secondKind (b : bool) : LookupKind := if b then secondTrue else secondFalse.
Lemma encNat_cells : forall n, map ofBool (encNat n) = ones n ++ [zero].
Proof.
  induction n as [|n ih]; [reflexivity |]. cbn [encNat map]. rewrite ih. reflexivity.
Qed.

Theorem gate_step : forall i j K w v L T,
  i < length v -> j < length v -> (T = [] \/ T = [blank]) ->
  i + j + length w + length v + 10 <= K ->
  exists t, t <= 256 * K * K /\
    Reaches candidate (cfg 36 L (one :: ones i ++ zero :: ones j ++ zero ::
      map ofBool w ++ separator :: map ofBool v ++ T)) t
      (cfg 36 (zero :: ones j ++ zero :: ones i ++ one :: L)
        (map ofBool w ++ separator :: map ofBool (v ++ [negb (Circuits.wire v i && Circuits.wire v j)]))).
Proof.
  intros i j K w v L T hi hj hT hK.
  set (r := encNat j ++ w).
  assert (he : map ofBool r = ones j ++ zero :: map ofBool w).
  { unfold r. rewrite map_app, encNat_cells. repeat rewrite <- app_assoc. reflexivity. }
  assert (hlen : length r = j + 1 + length w) by (unfold r; rewrite length_app, length_encNat; lia).
  assert (hK1 : i + length r + length v + length (lookupPrefix first 0) + 4 <= K)
    by (cbn [lookupPrefix length]; lia).
  destruct (lookup_success first 0 i K r v L T hi hK1) as [t1 [ht1 h1]].
  assert (hp : rev (lookupPrefix (secondKind (Circuits.wire v i)) i) = zero :: ones i).
  { unfold secondKind. destruct (Circuits.wire v i); unfold lookupPrefix, ones; cells; reflexivity. }
  assert (hpLen : length (lookupPrefix (secondKind (Circuits.wire v i)) i) = i + 1).
  { unfold secondKind. destruct (Circuits.wire v i); unfold lookupPrefix, ones; cells; lia. }
  assert (hK2 : j + length w + length v + length (lookupPrefix (secondKind (Circuits.wire v i)) i) + 4 <= K)
    by (rewrite hpLen; lia).
  destruct (lookup_success (secondKind (Circuits.wire v i)) i j K w v L T hj hK2) as [t2 [ht2 h2]].
  assert (hq : lookupInit (secondKind (Circuits.wire v i)) = lookupExit first (Circuits.wire v i)).
  { unfold secondKind. destruct (Circuits.wire v i); reflexivity. }
  assert (hx : lookupExit (secondKind (Circuits.wire v i)) (Circuits.wire v j) =
    appendSep (negb (Circuits.wire v i && Circuits.wire v j))).
  { unfold secondKind. destruct (Circuits.wire v i), (Circuits.wire v j); reflexivity. }
  pose proof (append_gate (negb (Circuits.wire v i && Circuits.wire v j)) i j w v L T hT) as h3.
  rewrite he in h1. cbn [lookupPrefix rev app] in h1. cells in h1.
  rewrite hp, hq, hx in h2. cells in h2. cells in h3. cells.
  pose proof (reaches_trans _ _ _ _ _ h1 (reaches_trans _ _ _ _ _ h2 h3)) as h.
  pose proof (R1 36 (lookupInit first) one blank _ _ _ _ eq_refl h) as h'.
  exists (S (t1 + (t2 + (2 * length w + 2 * length v + 2 * i + 2 * j + 8)))).
  split; [nia | exact h'].
Qed.


Theorem gate_reject : forall i j K w v L T,
  ~ (i < length v /\ j < length v) -> (T = [] \/ T = [blank]) ->
  i + j + length w + length v + 10 <= K ->
  exists t, t <= 256 * K * K /\
    Run candidate (cfg 36 L (one :: ones i ++ zero :: ones j ++ zero ::
      map ofBool w ++ separator :: map ofBool v ++ T)) t false.
Proof.
  intros i j K w v L T hb hT hK.
  set (r := encNat j ++ w).
  assert (he : map ofBool r = ones j ++ zero :: map ofBool w).
  { unfold r. rewrite map_app, encNat_cells. repeat rewrite <- app_assoc. reflexivity. }
  assert (hlen : length r = j + 1 + length w) by (unfold r; rewrite length_app, length_encNat; lia).
  assert (hK1 : i + length r + length v + length (lookupPrefix first 0) + 4 <= K)
    by (cbn [lookupPrefix length]; lia).
  destruct (Nat.lt_ge_cases i (length v)) as [hi | hi].
  - assert (hj : length v <= j) by lia.
    destruct (lookup_success first 0 i K r v L T hi hK1) as [t1 [ht1 h1]].
    assert (hp : rev (lookupPrefix (secondKind (Circuits.wire v i)) i) = zero :: ones i).
    { unfold secondKind. destruct (Circuits.wire v i); unfold lookupPrefix, ones; cells; reflexivity. }
    assert (hpLen : length (lookupPrefix (secondKind (Circuits.wire v i)) i) = i + 1).
    { unfold secondKind. destruct (Circuits.wire v i); unfold lookupPrefix, ones; cells; lia. }
    assert (hK2 : j + length w + length v + length (lookupPrefix (secondKind (Circuits.wire v i)) i) + 4 <= K)
      by (rewrite hpLen; lia).
    destruct (lookup_reject (secondKind (Circuits.wire v i)) i j K w v L T hj hT hK2) as [t2 [ht2 h2]].
    assert (hq : lookupInit (secondKind (Circuits.wire v i)) = lookupExit first (Circuits.wire v i)).
    { unfold secondKind. destruct (Circuits.wire v i); reflexivity. }
    rewrite he in h1. cbn [lookupPrefix rev app] in h1. cells in h1.
    rewrite hp, hq in h2. cells in h2. cells.
    exists (S (t1 + t2)). split; [nia |].
    eapply run_next; [apply (stepR 36 (lookupInit first) one blank); reflexivity |].
    exact (reaches_run _ _ _ _ _ _ h1 h2).
  - destruct (lookup_reject first 0 i K r v L T hi hT hK1) as [t [ht hr]].
    rewrite he in hr. cbn [lookupPrefix rev app] in hr. cells in hr. cells.
    exists (S t). split; [nia |].
    eapply run_next; [apply (stepR 36 (lookupInit first) one blank); reflexivity | exact hr].
Qed.

(** The induction covers every gate, including malformed forward references. *)
Theorem gate_loop : forall C v L T K,
  (T = [] \/ T = [blank]) ->
  length (encList encGate C) + length v + 10 <= K ->
  exists t, t <= 512 * (length C + 1) * K * K /\
    Run candidate (cfg 36 L
      (map ofBool (encList encGate C) ++ separator :: map ofBool v ++ T)) t
      (wfFromb (length v) C && Circuits.output v C).
Proof.
  induction C as [|[i j] C ih]; intros v L T K hT hK.
  - exists (length v + 3). split; [nia |].
    cbn [encList map app wfFromb Circuits.output Circuits.wires].
    apply gate_empty_padded. exact hT.
  - assert (hlen : length (encList encGate ((i,j) :: C)) = i + j + 3 + length (encList encGate C)).
    { cbn [encList length]. unfold encGate. rewrite !length_app, !length_encNat. cbn [fst snd]. lia. }
    assert (hK' : i + j + length (encList encGate C) + length v + 10 <= K) by lia.
    assert (he : map ofBool (encList encGate ((i,j) :: C)) =
      one :: ones i ++ zero :: ones j ++ zero :: map ofBool (encList encGate C)).
    { cbn [encList map]. unfold encGate. rewrite !map_app, !encNat_cells. cells. reflexivity. }
    destruct (Nat.lt_ge_cases i (length v)) as [hi | hi];
      destruct (Nat.lt_ge_cases j (length v)) as [hj | hj].
    + destruct (gate_step i j K (encList encGate C) v L T hi hj hT hK') as [t1 [ht1 h1]].
      assert (hK'' : length (encList encGate C) +
        length (v ++ [negb (Circuits.wire v i && Circuits.wire v j)]) + 10 <= K)
        by (rewrite length_app; cbn [length]; lia).
      destruct (ih (v ++ [negb (Circuits.wire v i && Circuits.wire v j)])
        (zero :: ones j ++ zero :: ones i ++ one :: L) [] K (or_introl eq_refl) hK'') as [t2 [ht2 h2]].
      exists (t1 + t2). split; [cbn [length]; nia |].
      rewrite he. cbn [wfFromb Circuits.output Circuits.wires].
      rewrite (proj2 (Nat.ltb_lt _ _) hi), (proj2 (Nat.ltb_lt _ _) hj).
      rewrite length_app in h2. cbn [length] in h2.
      assert (hout : Circuits.output v ((i,j) :: C) =
        Circuits.output (v ++ [negb (Circuits.wire v i && Circuits.wire v j)]) C) by reflexivity.
      rewrite hout. cbn [andb].
      cells in h1. cells in h2. cells. cells.
      exact (reaches_run _ _ _ _ _ _ h1 h2).
    + assert (hg : ~ (i < length v /\ j < length v)) by lia.
      destruct (gate_reject i j K (encList encGate C) v L T hg hT hK') as [t [ht hr]].
      exists t. split; [cbn [length]; nia |]. rewrite he. cbn [wfFromb].
      rewrite (proj2 (Nat.ltb_ge _ _) hj), andb_false_r. cells in hr. cells. cells. cbn [andb]. exact hr.
    + assert (hg : ~ (i < length v /\ j < length v)) by lia.
      destruct (gate_reject i j K (encList encGate C) v L T hg hT hK') as [t [ht hr]].
      exists t. split; [cbn [length]; nia |]. rewrite he. cbn [wfFromb].
      rewrite (proj2 (Nat.ltb_ge _ _) hi). cells in hr. cells. cells. cbn [andb]. exact hr.
    + assert (hg : ~ (i < length v /\ j < length v)) by lia.
      destruct (gate_reject i j K (encList encGate C) v L T hg hT hK') as [t [ht hr]].
      exists t. split; [cbn [length]; nia |]. rewrite he. cbn [wfFromb].
      rewrite (proj2 (Nat.ltb_ge _ _) hi). cells in hr. cells. cells. cbn [andb]. exact hr.
Qed.


Lemma whole_budget : forall a b c K,
  1 <= K -> a <= 4 * K -> b <= 64 * K * K -> c <= 512 * K * K * K ->
  a + (b + c) <= 1024 * K ^ 3.
Proof. intros. cbn [Nat.pow]. nia. Qed.

(** Universal correctness and cubic charged termination for the finite table. *)
Theorem verifier_run : forall x cert,
  exists t, t <= 1024 * (length x + length cert + 12)^3 /\
    Run candidate (pairedInput x cert) t (verifyCircuit x cert).
Proof.
  intros x cert. set (K := length x + length cert + 12).
  assert (hk : 1 <= K) by (unfold K; lia).
  assert (hs : 2 * length x + 2 <= 4 * K) by (unfold K; lia).
  destruct (decCircuit x) as [[n C]|] eqn:hd.
  - pose proof (decCircuit_sound _ _ _ hd) as hx.
    assert (hsyntax : CircuitSyntax.circuitSyntax x = true).
    { apply CircuitSyntax.circuitSyntax_iff_decCircuit. exists n, C. exact hd. }
    pose proof (valid_start x cert hsyntax) as hstart.
    assert (he : map ofBool x = ones n ++ zero :: map ofBool (encList encGate C)).
    { rewrite hx. unfold encCircuit. rewrite map_app, encNat_cells. cells. reflexivity. }
    assert (hlen : length x = n + 1 + length (encList encGate C)).
    { rewrite hx. unfold encCircuit. rewrite length_app, length_encNat. reflexivity. }
    assert (hn : n + 1 <= K) by (unfold K; lia).
    assert (hsize : n + length (encList encGate C) + length cert + 4 <= K) by (unfold K; lia).
    assert (hgK : length (encList encGate C) + length cert + 10 <= K) by (unfold K; lia).
    assert (hgLen : length C + 1 <= K).
    { pose proof (decCircuit_data_bounds _ _ _ hd) as [_ h]. unfold K. lia. }
    rewrite he in hstart. cells in hstart.
    destruct (Nat.eq_dec (length cert) n) as [hc | hc].
    + destruct (count_success n (encList encGate C) cert hc) as [t1 [ht1 h1]].
      destruct (gate_loop C cert (zero :: ones n ++ [blank]) [blank] K
        (or_intror eq_refl) hgK) as [t2 [ht2 h2]].
      assert (hb : t1 <= 64 * K * K) by nia.
      assert (hc' : t2 <= 512 * K * K * K) by nia.
      exists (2 * length x + 2 + (t1 + t2)). split.
      * apply whole_budget; assumption.
      * unfold verifyCircuit. rewrite hd, hc, Nat.eqb_refl, andb_true_r.
        rewrite hc in h2. cells in h1. cells in h2. cells.
        exact (reaches_run _ _ _ _ _ _ hstart (reaches_run _ _ _ _ _ _ h1 h2)).
    + destruct (count_reject n (encList encGate C) cert hc) as [t1 [ht1 h1]].
      assert (hb : t1 <= 64 * K * K) by nia.
      exists (2 * length x + 2 + t1). split.
      * pose proof (whole_budget _ _ 0 K hk hs hb ltac:(lia)) as h. cbn [Nat.add] in h. lia.
      * unfold verifyCircuit. rewrite hd, (proj2 (Nat.eqb_neq _ _) hc), andb_false_r.
        cells in h1. cells. cbn [andb]. exact (reaches_run _ _ _ _ _ _ hstart h1).
  - assert (hbad : CircuitSyntax.circuitSyntax x = false).
    { destruct (CircuitSyntax.circuitSyntax x) eqn:he; [|reflexivity].
      apply CircuitSyntax.circuitSyntax_iff_decCircuit in he. destruct he as [n [C h]]. rewrite hd in h. discriminate. }
    exists (length x + 1). split.
    + pose proof (whole_budget (length x + 1) 0 0 K hk ltac:(lia) ltac:(lia) ltac:(lia)) as h.
      cbn [Nat.add] in h. rewrite Nat.add_0_r in h. exact h.
    + unfold verifyCircuit. rewrite hd. apply malformed_reject. exact hbad.
Qed.

(** Every halting run has the specified answer and the same cubic bound. *)
Theorem verifier_correct : forall x cert t b,
  Run candidate (pairedInput x cert) t b ->
  t <= 1024 * (length x + length cert + 12)^3 /\ b = verifyCircuit x cert.
Proof.
  intros x cert t b hr. destruct (verifier_run x cert) as [u [hu hr']].
  destruct (run_deterministic _ _ _ _ _ _ hr hr') as [-> hb]. auto.
Qed.

(** Acceptance agrees exactly with the executable certificate check. *)
Theorem verifier_accepts : forall x cert,
  (exists t, Run candidate (pairedInput x cert) t true) <-> verifyCircuit x cert = true.
Proof.
  intros x cert. split.
  - intros [t hr]. pose proof (verifier_correct _ _ _ _ hr) as [_ hb]. symmetry. exact hb.
  - intro h. destruct (verifier_run x cert) as [t [_ hr]]. rewrite h in hr. exists t. exact hr.
Qed.
