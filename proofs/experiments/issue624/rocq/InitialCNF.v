From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import RunCNF LocalCNF MachineCNF SuccessorCNF CertificateCNF VerifierTableau FixedWindow.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
Import ListNotations.

(** Initial row wiring with a fixed number of clauses per certificate cell. *)
Module InitialCNF.
Import Complexity Machines Tableau LocalCNF MachineCNF SuccessorCNF.
Import CertificateCNF VerifierTableau FixedWindow.

Inductive Source := fixed (symbol : Symbol) | certificate (position : nat).
Definition sourceEval (a : Assignment) (s : Source) : Symbol :=
  match s with
  | fixed s => s
  | certificate i => if a (2 * i) then ofBool (a (2 * i + 1)) else blank
  end.
Definition sourceCNF base s : CNF :=
  match s with
  | fixed s => [[mkLit (base + symbolIndex s) true]]
  | certificate i =>
    [implies [mkLit (2 * i) false] [mkLit base true];
     implies [mkLit (2 * i) true; mkLit (2 * i + 1) false] [mkLit (base + 1) true];
     implies [mkLit (2 * i) true; mkLit (2 * i + 1) true] [mkLit (base + 2) true]]
  end.
Theorem sourceCNF_models : forall a base s,
  evalCNF a (sourceCNF base s) = true <-> a (base + symbolIndex (sourceEval a s)) = true.
Proof.
  intros a base [s|i].
  - cbn [sourceCNF sourceEval evalCNF evalClause evalLit].
    unfold evalLit. simpl. destruct (a (base + symbolIndex s)); reflexivity.
  - unfold sourceCNF, sourceEval, implies, negate. cbn [map app evalCNF evalClause evalLit var pos].
    unfold evalLit. simpl. rewrite Nat.add_0_r.
    destruct (a (i + i)), (a (i + i + 1)); cbn [ofBool symbolIndex];
      rewrite ?Nat.add_0_r; destruct (a base), (a (base + 1)), (a (base + 2)); reflexivity.
Qed.
Fixpoint tapeCNF base sources : CNF :=
  match sources with [] => [] | s :: rest => sourceCNF base s ++ tapeCNF (base + 4) rest end.
Fixpoint TapeSelected (a : Assignment) base xs : Prop :=
  match xs with [] => True | s :: rest => a (base + symbolIndex s) = true /\ TapeSelected a (base + 4) rest end.
Theorem tapeCNF_models : forall a base sources,
  evalCNF a (tapeCNF base sources) = true <-> TapeSelected a base (map (sourceEval a) sources).
Proof.
  intros a base sources. revert base. induction sources; intros; simpl; [tauto|].
  rewrite evalCNF_append, andb_true_iff, sourceCNF_models, IHsources. reflexivity.
Qed.
Theorem tapeSelected_iff : forall a base xs,
  TapeSelected a base xs <-> forall i, i < length xs -> a (base + 4 * i + symbolIndex (nth i xs blank)) = true.
Proof.
  intros a base xs. revert base. induction xs as [|s xs IH]; intro base; simpl.
  - split; [intros _ i hi; lia|auto].
  - rewrite IH. split.
    + intros [hs ht] [|i] hi; simpl; [rewrite Nat.add_0_r; exact hs|].
      change (a (base + 4 * S i + symbolIndex (nth i xs blank)) = true).
      replace (base + 4 * S i) with (base + 4 + 4 * i) by lia. apply ht. lia.
    + intro h. split; [pose proof (h 0 ltac:(lia)); simpl in H; rewrite Nat.add_0_r in H; exact H|].
      intros i hi. pose proof (h (S i) ltac:(lia)). simpl nth in H.
      change (a (base + 4 * S i + symbolIndex (nth i xs blank)) = true) in H.
      replace (base + 4 * S i) with (base + 4 + 4 * i) in H by lia. exact H.
Qed.
Fixpoint certificateSources start bound : list Source :=
  match bound with 0 => [] | S n => certificate start :: certificateSources (start + 1) n end.
Theorem certificateSources_length : forall start bound, length (certificateSources start bound) = bound.
Proof. intros start bound. revert start. induction bound; intros; simpl; auto. Qed.
Theorem certificateSources_eval : forall a start bound cert, Represents a start cert bound ->
  map (sourceEval a) (certificateSources start bound) = map ofBool cert ++ blanks (bound - length cert).
Proof.
  intros a start bound. revert start. induction bound as [|n IH]; intros start [|b cert] hr.
  - reflexivity.
  - contradiction.
  - destruct hr as [hp [hb ht]]. cbn [certificateSources map sourceEval]. rewrite hp, (IH _ [] ht).
    cbn [map length Nat.sub]. unfold blanks. rewrite Nat.sub_0_r. reflexivity.
  - destruct hr as [hp [hb ht]]. cbn [certificateSources map sourceEval]. rewrite hp, hb, (IH _ cert ht).
    cbn [map length Nat.sub]. reflexivity.
Qed.
Definition inputSources v x bound : list Source :=
  let bits := map (fun b => fixed (ofBool b)) x in
  match v with ignoreCertificate _ => bits | paired _ => bits ++ [fixed separator] ++ certificateSources 0 bound end.
Definition windowSources v x bound margin width : list Source :=
  repeat (fixed blank) margin ++ inputSources v x bound ++
    repeat (fixed blank) (width - margin - length (inputSources v x bound)).
Theorem windowSources_length : forall v x bound margin width,
  margin + length (inputSources v x bound) <= width -> length (windowSources v x bound margin width) = width.
Proof. intros. unfold windowSources. rewrite !length_app, !repeat_length. lia. Qed.
Lemma flatten_fit_initial : forall xs margin width, length xs + margin < width ->
  flatten (fitWindow (initialSymbols xs) margin width) =
    blanks margin ++ xs ++ blanks (width - margin - length xs).
Proof.
  intros [|s xs] margin width hw; unfold flatten, fitWindow, initialSymbols, span;
    cbn [state tapeLeft tapeHead tapeRight app length].
  - unfold blanks. rewrite rev_repeat, Nat.sub_0_r.
    replace (width - margin) with (S (width - 1 - margin)) by (simpl in hw; lia). reflexivity.
  - unfold blanks. rewrite rev_repeat.
    replace (width - (0 + 1 + length xs) - margin) with (width - margin - S (length xs)) by lia. reflexivity.
Qed.
Theorem windowSources_eval : forall np x a,
  evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true ->
  map (sourceEval a) (windowSources (np_verifier np) x (evalPoly (np_certBound np) (length x))
    (maxClock np (length x)) (windowWidth np (length x))) =
  flatten (fitWindow (verifierInitial (np_verifier np) x
    (decodeCertificate a 0 (evalPoly (np_certBound np) (length x))))
    (maxClock np (length x)) (windowWidth np (length x))).
Proof.
  intros np x a hf. set (B := evalPoly (np_certBound np) (length x)).
  set (T := maxClock np (length x)). set (W := windowWidth np (length x)).
  set (cert := decodeCertificate a 0 B).
  pose proof (decodeCertificate_length a 0 B) as hc. fold cert in hc.
  pose proof (certificateSources_eval a 0 B cert (proj1 (certificateCNF_models a 0 B) hf)) as hs.
  assert (hbl : forall k, map (sourceEval a) (repeat (fixed blank) k) = blanks k).
  { intro k. rewrite map_repeat. reflexivity. }
  destruct (np_verifier np) as [m|m] eqn:hv; cbn [verifierInitial].
  - unfold initial. rewrite flatten_fit_initial by (rewrite length_map; unfold W, windowWidth; fold B T; lia).
    unfold windowSources, inputSources. rewrite !map_app, !hbl, map_map, !length_map. reflexivity.
  - unfold pairedInput. rewrite flatten_fit_initial by
      (rewrite !length_app, !length_map; simpl length; unfold W, windowWidth; fold B T; lia).
    unfold windowSources, inputSources. rewrite !map_app, !hbl, map_map, hs.
    cbn [map sourceEval]. rewrite !length_app, !length_map, certificateSources_length. simpl length.
    assert (he : blanks (B - length cert) ++ blanks (W - T - (length x + 1 + B)) =
      blanks (W - T - (length x + 1 + length cert))).
    { unfold blanks. rewrite <- repeat_app. f_equal. unfold W, windowWidth. fold B T. lia. }
    rewrite <- !app_assoc, !Nat.add_assoc. rewrite he. reflexivity.
Qed.
Definition initialCNF base states margin sources : CNF :=
  (rowCNF base states (length sources) ++
    [[mkLit base true]; [mkLit (base + states + margin) true]]) ++
    tapeCNF (base + states + length sources) sources.
Theorem initialCNF_models : forall a base states margin sources c,
  span c = length sources -> state c = 0 -> length (tapeLeft c) = margin ->
  flatten c = map (sourceEval a) sources ->
  (evalCNF a (initialCNF base states margin sources) = true <-> RowRepresents a base states (length sources) c).
Proof.
  intros a base states margin sources c hw hq hh ht.
  unfold initialCNF. rewrite !evalCNF_append, !andb_true_iff, tapeCNF_models.
  cbn [evalCNF evalClause]. unfold evalLit. cbn [var pos].
  rewrite !orb_false_r, andb_true_r, andb_true_iff, !Bool.eqb_true_iff.
  split.
  - intros [[hr [hq' hh']] ht']. apply rowCNF_models in hr.
    assert (hstate : state (decodeRow a base states (length sources)) = state c).
    { rewrite hq. symmetry. apply (proj2 (proj2 (proj1 (proj2 hr)))); [pose proof (proj1 (proj1 (proj2 hr))); lia|].
      rewrite Nat.add_0_r. exact hq'. }
    assert (hhead : length (tapeLeft (decodeRow a base states (length sources))) = length (tapeLeft c)).
    { rewrite hh. symmetry. apply (proj2 (proj2 (proj1 (proj2 (proj2 hr)))));
        [unfold span in hw; lia|exact hh']. }
    assert (hflat : flatten (decodeRow a base states (length sources)) = flatten c).
    { apply nth_ext with (d := blank) (d' := blank).
      - rewrite !flatten_length, (proj1 hr), hw. reflexivity.
      - intros i hi. rewrite flatten_length, (proj1 hr) in hi.
        pose proof (proj2 (proj2 (proj2 hr)) i hi) as hsel.
        pose proof (proj1 (tapeSelected_iff a _ _) ht') as htp.
        pose proof (htp i ltac:(rewrite length_map; exact hi)) as hp.
        rewrite <- ht in hp.
        pose proof (proj2 (proj2 hsel) (symbolIndex (nth i (flatten c) blank))
          (symbolIndex_lt _) ltac:(unfold tapeBase; exact hp)) as he.
        apply (f_equal symbolOfIndex) in he. rewrite !symbolOfIndex_index in he. symmetry. exact he. }
    pose proof (flatten_injective _ c hstate hhead hflat) as he. rewrite he in hr. exact hr.
  - intro hr. split.
    + split; [eapply rowRepresents_models; exact hr|]. split.
      * pose proof (proj1 (proj2 (proj1 (proj2 hr)))) as hp. rewrite hq, Nat.add_0_r in hp. exact hp.
      * pose proof (proj1 (proj2 (proj1 (proj2 (proj2 hr))))) as hp. rewrite hh in hp. exact hp.
    + apply tapeSelected_iff. intros i hi. rewrite length_map in hi.
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hr)) i hi))) as hp.
      unfold tapeBase, cell in hp. rewrite <- ht. exact hp.
Qed.

Definition SourceBound bound s : Prop := match s with fixed _ => True | certificate i => i < bound end.
Theorem sourceCNF_length : forall base s, length (sourceCNF base s) <= 3.
Proof. intros base [s|i]; simpl; lia. Qed.
Theorem sourceCNF_bounds : forall base bound limit s,
  base + 4 <= limit -> 2 * bound <= limit -> SourceBound bound s ->
  VarsBelow limit (sourceCNF base s) /\ forall c, In c (sourceCNF base s) -> length c <= 3.
Proof.
  intros base bound limit [s|i] hb hc hs; split.
  - intros c [he|[]] l hl. subst c. destruct hl as [he|[]]. subst l. simpl.
    pose proof (symbolIndex_lt s). lia.
  - intros c [he|[]]. subst c. simpl. lia.
  - unfold SourceBound in hs. intros c h l hl. cbn [sourceCNF] in h.
    destruct h as [he|[he|[he|[]]]]; subst c; unfold implies, negate in hl; simpl in hl;
      intuition (subst l; simpl; lia).
  - intros c h. cbn [sourceCNF] in h.
    destruct h as [he|[he|[he|[]]]]; subst c; unfold implies; simpl; lia.
Qed.
Theorem tapeCNF_length : forall base sources, length (tapeCNF base sources) <= 3 * length sources.
Proof.
  intros base sources. revert base. induction sources as [|s rest IH]; intro base; simpl; [lia|].
  rewrite length_app. pose proof (sourceCNF_length base s). specialize (IH (base + 4)). lia.
Qed.
Theorem tapeCNF_bounds : forall base bound limit sources,
  base + 4 * length sources <= limit -> 2 * bound <= limit ->
  (forall s, In s sources -> SourceBound bound s) ->
  VarsBelow limit (tapeCNF base sources) /\ forall c, In c (tapeCNF base sources) -> length c <= 3.
Proof.
  intros base bound limit sources. revert base. induction sources as [|s rest IH]; intros base hb hc hs.
  - split; intros c []; contradiction.
  - destruct (sourceCNF_bounds base bound limit s ltac:(simpl in hb; lia) hc (hs s (or_introl eq_refl))) as [hhv hhw].
    destruct (IH (base + 4) ltac:(simpl in hb; lia) hc ltac:(intros; apply hs; right; assumption)) as [htv htw].
    cbn [tapeCNF]. split.
    + intros c h l hl. apply in_app_or in h. destruct h; [eapply hhv|eapply htv]; eauto.
    + intros c h. apply in_app_or in h. destruct h; [apply hhw|apply htw]; assumption.
Qed.
Theorem certificateSources_bound : forall start bound s,
  In s (certificateSources start bound) -> SourceBound (start + bound) s.
Proof.
  intros start bound. revert start. induction bound as [|k IH]; intros start s hs; [contradiction|].
  simpl in hs. destruct hs as [he|hs].
  - subst s. unfold SourceBound. lia.
  - replace (start + S k) with (start + 1 + k) by lia. apply IH. exact hs.
Qed.
Theorem windowSources_bound : forall v x bound margin width s,
  In s (windowSources v x bound margin width) -> SourceBound bound s.
Proof.
  intros v x bound margin width s hs. unfold windowSources in hs.
  apply in_app_or in hs. destruct hs as [hs|hs]; [apply repeat_spec in hs; subst; exact I|].
  apply in_app_or in hs. destruct hs as [hs|hs]; [|apply repeat_spec in hs; subst; exact I].
  destruct v; cbn [inputSources] in hs.
  - apply in_map_iff in hs. destruct hs as [b [he _]]. subst s. exact I.
  - apply in_app_or in hs. destruct hs as [hs|hs].
    + apply in_map_iff in hs. destruct hs as [b [he _]]. subst s. exact I.
    + destruct hs as [he|hs]; [subst; exact I|].
      replace bound with (0 + bound) by lia. apply certificateSources_bound. exact hs.
Qed.
Theorem initialCNF_length : forall base states margin sources,
  length (initialCNF base states margin sources) <=
    states * states + length sources * length sources + 20 * length sources + 4.
Proof.
  intros. pose proof (rowCNF_length base states (length sources)).
  pose proof (tapeCNF_length (base + states + length sources) sources).
  unfold initialCNF. rewrite !length_app.
  change (length (rowCNF base states (length sources)) + 2 +
    length (tapeCNF (base + states + length sources) sources) <=
      states * states + length sources * length sources + 20 * length sources + 4). lia.
Qed.
Theorem initialCNF_bounds : forall base states margin bound sources,
  margin < length sources -> 2 * bound <= base -> (forall s, In s sources -> SourceBound bound s) ->
  VarsBelow (base + states + 5 * length sources) (initialCNF base states margin sources) /\
  forall c, In c (initialCNF base states margin sources) -> length c <= states + length sources + 6.
Proof.
  intros base states margin bound sources hm hc hs.
  destruct (rowCNF_bounds base states (length sources)) as [hrv hrw].
  destruct (tapeCNF_bounds (base + states + length sources) bound
    (base + states + 5 * length sources) sources ltac:(lia) ltac:(lia) hs) as [htv htw].
  unfold initialCNF. split.
  - intros c h l hl. apply in_app_or in h. destruct h as [h|h]; [|apply (htv c h l hl)].
    apply in_app_or in h. destruct h as [h|h]; [apply (hrv c h l hl)|].
    destruct h as [he|[he|[]]]; subst c; destruct hl as [he|[]]; subst l; simpl; lia.
  - intros c h. apply in_app_or in h. destruct h as [h|h]; [|pose proof (htw c h); lia].
    apply in_app_or in h. destruct h as [h|h]; [apply (hrw c h)|].
    destruct h as [he|[he|[]]]; subst c; simpl; lia.
Qed.
Definition initialPolynomial states (b w : Polynomial) : Polynomial :=
  let c := fun n => {| coefficient := n; degree := 0 |} in
  let q := c states in
  let count := polyAdd (polyAdd (polyAdd (polyMul q q) (polyMul w w)) (polyMul (c 20) w)) (c 4) in
  let width := polyAdd (polyAdd q w) (c 6) in
  let variables := polyAdd (polyAdd (polyAdd b q) (polyMul (c 5) w)) (c 1) in
  polyMul (polyMul (c 2) count) (polyAdd (c 1) (polyMul width variables)).
Theorem initialCNF_polynomial_size : forall states b w n base margin bound sources,
  base <= evalPoly b n -> length sources <= evalPoly w n ->
  margin < length sources -> 2 * bound <= base -> (forall s, In s sources -> SourceBound bound s) ->
  length (encodeCNF (initialCNF base states margin sources)) <= evalPoly (initialPolynomial states b w) n.
Proof.
  intros states b w n base margin bound sources hb hw hm hc hs.
  assert (add : forall p q u v, u <= evalPoly p n -> v <= evalPoly q n -> u + v <= evalPoly (polyAdd p q) n).
  { intros. eapply Nat.le_trans; [apply Nat.add_le_mono; eassumption|apply polyAdd_eval]. }
  assert (mul : forall p q u v, u <= evalPoly p n -> v <= evalPoly q n -> u * v <= evalPoly (polyMul p q) n).
  { intros. rewrite <- polyMul_eval. apply Nat.mul_le_mono; assumption. }
  assert (const : forall k, k <= evalPoly {| coefficient := k; degree := 0 |} n).
  { intros. unfold evalPoly. simpl. lia. }
  pose proof (add _ _ _ _ (add _ _ _ _ (add _ _ _ _
    (mul _ _ _ _ (const states) (const states)) (mul _ _ _ _ hw hw))
    (mul _ _ _ _ (const 20) hw)) (const 4)) as hcount.
  pose proof (add _ _ _ _ (add _ _ _ _ (const states) hw) (const 6)) as hwidth.
  pose proof (add _ _ _ _ (add _ _ _ _ (add _ _ _ _ hb (const states))
    (mul _ _ _ _ (const 5) hw)) (const 1)) as hvars.
  pose proof (mul _ _ _ _ (mul _ _ _ _ (const 2) hcount)
    (add _ _ _ _ (const 1) (mul _ _ _ _ hwidth hvars))) as hsize.
  destruct (initialCNF_bounds base states margin bound sources hm hc hs) as [hv hcw].
  pose proof (cnf_encoded_size _ _ _ hv hcw) as henc.
  pose proof (initialCNF_length base states margin sources) as hlen.
  eapply Nat.le_trans; [exact henc|]. eapply Nat.le_trans; [|exact hsize].
  apply Nat.mul_le_mono_r. lia.
Qed.

End InitialCNF.
