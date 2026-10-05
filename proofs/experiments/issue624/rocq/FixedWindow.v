From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import CertificateCNF VerifierTableau.
Import ListNotations.

(** Fixed windows for the shared LocalTrace, with a checked two-way blank
    padding simulation. No new trace semantics or left boundary is assumed. *)
Module FixedWindow.
Import Complexity Machines Tableau CertificateCNF VerifierTableau.

Definition TapeEquivalent (c d : Config) : Prop :=
  state c = state d /\ tapeHead c = tapeHead d /\
  BlankPad (tapeLeft c) (tapeLeft d) /\ BlankPad (tapeRight c) (tapeRight d).

Theorem tapeEquivalent_symm : forall c d,
  TapeEquivalent c d -> TapeEquivalent d c.
Proof.
  intros c d [hs [hh [hl hr]]]. unfold TapeEquivalent.
  repeat split; try congruence; apply blankPad_symm; assumption.
Qed.

Theorem tapeEquivalent_moveHead : forall c d,
  TapeEquivalent c d -> forall q w dir,
  TapeEquivalent (moveHead c q w dir) (moveHead d q w dir).
Proof.
  intros [cs cl ch cr] [ds dl dh dr] [_ [_ [hl hr]]] q w dir.
  destruct dir; cbn [moveHead].
  - destruct cl as [|a l], dl as [|b s]; cbn [moveHead]; unfold TapeEquivalent;
      cbn [state tapeHead tapeLeft tapeRight].
    + repeat split; try reflexivity; [apply blankPad_refl|apply blankPad_cons; exact hr].
    + destruct (blankPad_nil_cons b s hl) as [hb ht].
      split; [reflexivity|]. split; [congruence|]. split; [exact ht|apply blankPad_cons; exact hr].
    + pose proof (blankPad_symm _ _ hl) as hls.
      destruct (blankPad_nil_cons a l hls) as [ha ht].
      split; [reflexivity|]. split; [congruence|]. split; [apply blankPad_symm; exact ht|apply blankPad_cons; exact hr].
    + destruct (blankPad_cons_cons a b l s hl) as [hab ht].
      split; [reflexivity|]. split; [congruence|]. split; [exact ht|apply blankPad_cons; exact hr].
  - destruct cr as [|a r], dr as [|b s]; cbn [moveHead]; unfold TapeEquivalent;
      cbn [state tapeHead tapeLeft tapeRight].
    + repeat split; try reflexivity; [apply blankPad_cons; exact hl|apply blankPad_refl].
    + destruct (blankPad_nil_cons b s hr) as [hb ht].
      split; [reflexivity|]. split; [congruence|]. split; [apply blankPad_cons; exact hl|exact ht].
    + pose proof (blankPad_symm _ _ hr) as hrs.
      destruct (blankPad_nil_cons a r hrs) as [ha ht].
      split; [reflexivity|]. split; [congruence|]. split; [apply blankPad_cons; exact hl|apply blankPad_symm; exact ht].
    + destruct (blankPad_cons_cons a b r s hr) as [hab ht].
      split; [reflexivity|]. split; [congruence|]. split; [apply blankPad_cons; exact hl|exact ht].
  - unfold TapeEquivalent. cbn [state tapeHead tapeLeft tapeRight]. auto.
Qed.

Theorem tapeEquivalent_step : forall m c d,
  TapeEquivalent c d ->
  (forall b, step m c = inl b -> step m d = inl b) /\
  (forall c', step m c = inr c' ->
    exists d', step m d = inr d' /\ TapeEquivalent c' d').
Proof.
  intros m c d he. destruct he as [hq [hh [hl hr]]].
  assert (hi : instruction m (state c) (tapeHead c) =
      instruction m (state d) (tapeHead d)) by congruence.
  unfold step. rewrite hi.
  destruct (instruction m (state d) (tapeHead d)) as [b|q w dir].
  - split; intros; [assumption|discriminate].
  - split; [intros; discriminate|]. intros c' hc'. inversion hc'; subst c'.
    exists (moveHead d q w dir). split; [reflexivity|].
    apply tapeEquivalent_moveHead. unfold TapeEquivalent. auto.
Qed.

Theorem run_of_tapeEquivalent : forall m c t b,
  Run m c t b -> forall d, TapeEquivalent c d -> Run m d t b.
Proof.
  intros m c t b h. induction h as [c b hs|c c' t b hs ht IH]; intros d he.
  - apply run_halt. apply (proj1 (tapeEquivalent_step m c d he)); exact hs.
  - destruct (proj2 (tapeEquivalent_step m c d he) c' hs) as [d' [hd he']].
    apply run_next with d'; [exact hd|]. apply IH. exact he'.
Qed.

Definition fitWindow (c : Config) (margin width : nat) : Config :=
  {| state := state c; tapeLeft := tapeLeft c ++ blanks margin;
     tapeHead := tapeHead c;
     tapeRight := tapeRight c ++ blanks (width - span c - margin) |}.

Theorem fitWindow_equivalent : forall c margin width,
  TapeEquivalent c (fitWindow c margin width).
Proof.
  intros c margin width. unfold TapeEquivalent, fitWindow. simpl.
  repeat split; try reflexivity.
  - exists (tapeLeft c), 0, margin. simpl. rewrite app_nil_r. auto.
  - exists (tapeRight c), 0, (width - span c - margin).
    simpl. rewrite app_nil_r. auto.
Qed.

Theorem run_fitWindow_iff : forall m c t b margin width,
  Run m (fitWindow c margin width) t b <-> Run m c t b.
Proof.
  intros m c t b margin width. split; intro hr.
  - eapply run_of_tapeEquivalent; [exact hr|].
    apply tapeEquivalent_symm. apply fitWindow_equivalent.
  - eapply run_of_tapeEquivalent; [exact hr|]. apply fitWindow_equivalent.
Qed.

Theorem fitWindow_span : forall c margin width,
  span c + 2 * margin <= width -> span (fitWindow c margin width) = width.
Proof.
  intros c margin width h. unfold fitWindow, span, blanks in *.
  simpl. repeat rewrite length_app. repeat rewrite repeat_length. lia.
Qed.

Theorem fitWindow_reserve : forall c margin width,
  span c + 2 * margin <= width ->
  margin <= length (tapeLeft (fitWindow c margin width)) /\
  margin <= length (tapeRight (fitWindow c margin width)).
Proof.
  intros c margin width h. unfold fitWindow, span, blanks in *.
  simpl. repeat rewrite length_app. repeat rewrite repeat_length. lia.
Qed.

Lemma run_pos : forall m c t b, Run m c t b -> 0 < t.
Proof. intros m c t b h. destruct h; lia. Qed.

Lemma step_window : forall m c d k,
  step m c = inr d -> k + 1 <= length (tapeLeft c) ->
  k + 1 <= length (tapeRight c) ->
  span d = span c /\ k <= length (tapeLeft d) /\ k <= length (tapeRight d).
Proof.
  intros m [q l a r] d k hs hl hr. destruct l as [|l ls]; [simpl in hl; lia|].
  destruct r as [|r rs]; [simpl in hr; lia|].
  unfold step in hs. cbn [state tapeHead] in hs.
  destruct (instruction m q a) as [b|next w dir]; [discriminate|].
  inversion hs; subst d. destruct dir; unfold moveHead, span in *; simpl in *; lia.
Qed.

Theorem trace_window_of_run : forall m c t b,
  Run m c t b -> t - 1 <= length (tapeLeft c) -> t - 1 <= length (tapeRight c) ->
  exists trace : list Config, hd_error trace = Some c /\ length trace = t /\
    localTrace m b trace /\ forall d, In d trace -> span d = span c.
Proof.
  intros m c t b h. induction h as [c b hs|c d t b hs hd IH]; intros hl hr.
  - exists [c]. repeat split; try reflexivity; [exact hs|].
    intros d [he|[]]. subst. reflexivity.
  - pose proof (run_pos m d t b hd) as hp.
    assert (hcl : t - 1 + 1 <= length (tapeLeft c)) by lia.
    assert (hcr : t - 1 + 1 <= length (tapeRight c)) by lia.
    destruct (step_window m c d (t - 1) hs hcl hcr) as [hw [hdl hdr]].
    destruct (IH hdl hdr) as [trace [hhead [hlen [hlocal hwidth]]]].
    destruct trace as [|first rest]; [discriminate|].
    simpl in hhead. inversion hhead. subst first.
    exists (c :: d :: rest). split; [reflexivity|]. split; [simpl in *; lia|].
    split; [simpl; auto|]. intros e [he|he]; [subst; reflexivity|].
    rewrite <- hw. apply hwidth. exact he.
Qed.

Lemma accepting_step_state_lt : forall m c,
  step m c = inl true -> state c < length (program m).
Proof.
  intros m c h. destruct (lt_dec (state c) (length (program m))); [assumption|].
  unfold step in h. rewrite (instruction_of_length_le m (state c) (tapeHead c)) in h;
    [discriminate|lia].
Qed.

Theorem accepting_trace_state_lt : forall m trace,
  localTrace m true trace -> forall c, In c trace -> state c < length (program m).
Proof.
  intros m trace. induction trace as [|c rest IH]; intros ht e he; [contradiction|].
  destruct rest as [|d tail].
  - simpl in he. destruct he as [he|[]]. subst e. apply accepting_step_state_lt. exact ht.
  - destruct ht as [hs ht]. destruct he as [he|he].
    + subst e. eapply state_lt_of_step; eauto.
    + apply IH; assumption.
Qed.

Definition windowWidth (np : ClassNP) (n : nat) : nat :=
  n + evalPoly (np_certBound np) n + 2 * maxClock np n + 3.

Definition windowPolynomial (np : ClassNP) : Polynomial :=
  {| coefficient := coefficient (np_certBound np) + 2 * coefficient (clockPolynomial np) + 4;
     degree := degree (np_certBound np) + degree (clockPolynomial np) + 1 |}.

Theorem windowWidth_polynomial : forall np n,
  windowWidth np n <= evalPoly (windowPolynomial np) n.
Proof.
  intros np n. set (d := degree (np_certBound np) + degree (clockPolynomial np) + 1).
  assert (hc : evalPoly (np_certBound np) n <= coefficient (np_certBound np) * (n + 1) ^ d).
  { unfold evalPoly. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_r; unfold d; lia. }
  assert (ht : evalPoly (clockPolynomial np) n <= coefficient (clockPolynomial np) * (n + 1) ^ d).
  { unfold evalPoly. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_r; unfold d; lia. }
  assert (hn : n + 1 <= (n + 1) ^ d).
  { replace (n + 1) with ((n + 1) ^ 1) at 1 by (simpl; lia).
    apply Nat.pow_le_mono_r; unfold d; lia. }
  pose proof (maxClock_polynomial np n) as hclock.
  unfold evalPoly in hc, ht, hclock.
  unfold windowWidth, windowPolynomial, evalPoly. cbn [coefficient degree]. fold d. nia.
Qed.

Definition WindowVerifierTableau (np : ClassNP) (x : Word) (a : Assignment)
    (trace : list Config) : Prop :=
  let cert := decodeCertificate a 0 (evalPoly (np_certBound np) (length x)) in
  let clock := maxClock np (length x) in
  let width := windowWidth np (length x) in
  evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true /\
  hd_error trace = Some (fitWindow (verifierInitial (np_verifier np) x cert) clock width) /\
  length trace <= clock /\ localTrace (verifierMachine (np_verifier np)) true trace /\
  forall d, In d trace -> span d = width.

Theorem windowVerifierTableau_iff_language : forall np x,
  (exists a trace, WindowVerifierTableau np x a trace) <-> np_language np x = true.
Proof.
  intros np x. split.
  - intros [a [trace [_ [hhead [_ [hlocal _]]]]]].
    pose proof (decodeCertificate_length a 0 (evalPoly (np_certBound np) (length x))) as hc.
    assert (hr : Run (verifierMachine (np_verifier np))
      (fitWindow (verifierInitial (np_verifier np) x
        (decodeCertificate a 0 (evalPoly (np_certBound np) (length x))))
        (maxClock np (length x)) (windowWidth np (length x))) (length trace) true).
    { apply (proj1 (localTrace_iff_run _ _ _ true)). exists trace. auto. }
    apply run_fitWindow_iff in hr. apply verifierRun_iff in hr.
    apply (proj2 (np_correct np x)). exists (decodeCertificate a 0 (evalPoly (np_certBound np) (length x))), (length trace).
    split; [exact hc|]. split; [|exact hr]. apply acceptingRun_timeLimit; assumption.
  - intro hx. destruct (proj1 (np_correct np x) hx) as [cert [t [hc [ht hv]]]].
    pose proof (verifierTimeLimit_le np x cert hc) as hclock.
    assert (hfit : span (verifierInitial (np_verifier np) x cert) +
      2 * maxClock np (length x) <= windowWidth np (length x)).
    { pose proof (verifierInitial_span (np_verifier np) x cert).
      unfold windowWidth. lia. }
    assert (hr : Run (verifierMachine (np_verifier np))
      (fitWindow (verifierInitial (np_verifier np) x cert)
        (maxClock np (length x)) (windowWidth np (length x))) t true).
    { apply run_fitWindow_iff. apply verifierRun_iff. exact hv. }
    destruct (fitWindow_reserve _ _ _ hfit) as [hl hright].
    destruct (trace_window_of_run _ _ _ _ hr ltac:(lia) ltac:(lia))
      as [trace [hhead [hlen [hlocal hwidth]]]].
    exists (encodeCertificate cert), trace. unfold WindowVerifierTableau.
    rewrite (decode_encodeCertificate cert _ hc).
    split; [apply encodeCertificate_models; exact hc|]. split; [exact hhead|].
    split; [lia|]. split; [exact hlocal|]. intros d hd.
    rewrite (hwidth d hd). apply fitWindow_span. exact hfit.
Qed.

End FixedWindow.
