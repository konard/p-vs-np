From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import
  LocalCNF MachineCNF SuccessorCNF RunCNF CertificateCNF VerifierTableau FixedWindow InitialCNF.
Import ListNotations.

(** Full bounded-verifier tableau and its model correspondence. The reduction
    machine and hardness assembly require separate charged machine proofs. *)
Module CookLevin.
Import Complexity Machines Tableau LocalCNF MachineCNF SuccessorCNF.
Import CertificateCNF VerifierTableau FixedWindow InitialCNF.

Definition rowBase (np : ClassNP) (x : Word) := 2 * evalPoly (np_certBound np) (length x) + 1.
Definition sources (np : ClassNP) (x : Word) :=
  windowSources (np_verifier np) x (evalPoly (np_certBound np) (length x))
    (maxClock np (length x)) (windowWidth np (length x)).
Definition initialRow (np : ClassNP) (x : Word) (a : Assignment) :=
  fitWindow (verifierInitial (np_verifier np) x (decodeCertificate a 0 (evalPoly (np_certBound np) (length x))))
    (maxClock np (length x)) (windowWidth np (length x)).
Definition tableauCNF (np : ClassNP) (x : Word) : CNF :=
  (certificateCNF 0 (evalPoly (np_certBound np) (length x)) ++
    initialCNF (rowBase np x) (length (program (verifierMachine (np_verifier np))))
      (maxClock np (length x)) (sources np x)) ++
    RunCNF.runCNF (verifierMachine (np_verifier np)) (rowBase np x)
      (windowWidth np (length x)) (maxClock np (length x)).
Definition decodeTrace (np : ClassNP) (x : Word) (a : Assignment) : list Config :=
  RunCNF.decodeTrace (verifierMachine (np_verifier np)) (rowBase np x)
    (windowWidth np (length x)) (maxClock np (length x)) a.

Theorem sources_length : forall np x, length (sources np x) = windowWidth np (length x).
Proof.
  intros. apply windowSources_length. destruct (np_verifier np); unfold inputSources;
    rewrite ?length_app, ?length_map, ?certificateSources_length; simpl length;
    unfold windowWidth; lia.
Qed.
Theorem initialRow_span : forall np x a, span (initialRow np x a) = windowWidth np (length x).
Proof.
  intros. apply fitWindow_span.
  pose proof (verifierInitial_span (np_verifier np) x (decodeCertificate a 0 (evalPoly (np_certBound np) (length x)))).
  pose proof (decodeCertificate_length a 0 (evalPoly (np_certBound np) (length x))).
  unfold windowWidth. lia.
Qed.
Theorem initialCNF_row : forall np x a,
  evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true ->
  (evalCNF a (initialCNF (rowBase np x) (length (program (verifierMachine (np_verifier np))))
    (maxClock np (length x)) (sources np x)) = true <->
  RowRepresents a (rowBase np x) (length (program (verifierMachine (np_verifier np))))
    (windowWidth np (length x)) (initialRow np x a)).
Proof.
  intros np x a hf. rewrite <- sources_length. apply initialCNF_models.
  - rewrite initialRow_span, sources_length. reflexivity.
  - unfold initialRow, fitWindow, verifierInitial, initial, pairedInput.
    destruct (np_verifier np); destruct x; reflexivity.
  - unfold initialRow, fitWindow, verifierInitial, initial, pairedInput.
    destruct (np_verifier np); destruct x; cbn [map initialSymbols tapeLeft app length];
      unfold blanks; rewrite repeat_length; reflexivity.
  - symmetry. apply windowSources_eval. exact hf.
Qed.
Theorem tableauCNF_unfold : forall np x a,
  evalCNF a (tableauCNF np x) = true <->
    evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true /\
    evalCNF a (initialCNF (rowBase np x) (length (program (verifierMachine (np_verifier np))))
      (maxClock np (length x)) (sources np x)) = true /\
    evalCNF a (RunCNF.runCNF (verifierMachine (np_verifier np)) (rowBase np x)
      (windowWidth np (length x)) (maxClock np (length x))) = true.
Proof. intros. unfold tableauCNF. rewrite !evalCNF_append, !andb_true_iff. tauto. Qed.
Theorem tableauCNF_sound : forall np x a, evalCNF a (tableauCNF np x) = true ->
  WindowVerifierTableau np x a (decodeTrace np x a).
Proof.
  intros np x a hf. apply tableauCNF_unfold in hf. destruct hf as [hc [hi hr]].
  apply (proj1 (initialCNF_row np x a hc)) in hi.
  destruct (RunCNF.runCNF_sound _ _ _ _ a hr) as [hrep hl].
  unfold WindowVerifierTableau. split; [exact hc|]. split.
  - unfold decodeTrace. destruct (maxClock np (length x)) eqn:ht; [discriminate hr|].
    cbn [RunCNF.decodeTrace hd_error]. rewrite (decodeRow_represents a _ _ _ _ hi).
    unfold initialRow. rewrite ht. reflexivity.
  - split; [apply RunCNF.decodeTrace_length|]. split; [exact hl|].
    eapply RunCNF.traceRepresents_width. exact hrep.
Qed.

(** Certificate slots stay below the row blocks in the joint model. *)
Definition jointAssignment (np : ClassNP) (x : Word) (a : Assignment) (trace : list Config) : Assignment :=
  fun v => if v <? rowBase np x then a v else
    RunCNF.traceAssignment (rowBase np x) (length (program (verifierMachine (np_verifier np))))
      (windowWidth np (length x)) trace v.
Theorem decodeCertificate_congr : forall a b start bound,
  (forall v, 2 * start <= v -> v < 2 * (start + bound) -> a v = b v) ->
  decodeCertificate a start bound = decodeCertificate b start bound.
Proof.
  intros a b start bound. revert start. induction bound as [|k IH]; intros start he; [reflexivity|].
  pose proof (he (2 * start) ltac:(lia) ltac:(lia)) as hp.
  pose proof (he (2 * start + 1) ltac:(lia) ltac:(lia)) as hv.
  cbn [decodeCertificate]. rewrite hp, hv. destruct (b (2 * start)); [|reflexivity].
  f_equal. apply IH. intros v hl hu. apply he; lia.
Qed.
Theorem tableauCNF_complete : forall np x a trace, WindowVerifierTableau np x a trace ->
  exists b, evalCNF b (tableauCNF np x) = true /\
    decodeCertificate b 0 (evalPoly (np_certBound np) (length x)) =
      decodeCertificate a 0 (evalPoly (np_certBound np) (length x)) /\ decodeTrace np x b = trace.
Proof.
  intros np x a trace [hc [hh [hb [hl hw]]]]. set (b := jointAssignment np x a trace).
  assert (he : forall v, v < rowBase np x -> b v = a v).
  { intros v hv. unfold b, jointAssignment. rewrite (proj2 (Nat.ltb_lt _ _) hv). reflexivity. }
  assert (hcert : evalCNF b (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true).
  { rewrite (evalCNF_congr b a (rowBase np x) _ he).
    - exact hc.
    - unfold rowBase. apply certificateCNF_variables. }
  assert (hd : decodeCertificate b 0 (evalPoly (np_certBound np) (length x)) =
    decodeCertificate a 0 (evalPoly (np_certBound np) (length x))).
  { apply decodeCertificate_congr. intros v _ hv. apply he. unfold rowBase. lia. }
  assert (hne : trace <> []) by (intro h; subst; contradiction).
  pose proof (RunCNF.traceAssignment_represents (rowBase np x)
    (length (program (verifierMachine (np_verifier np)))) (windowWidth np (length x)) trace hne
    ltac:(intros c h; split; [apply hw; exact h|eapply accepting_trace_state_lt; eauto])) as hrep.
  assert (hjrep : RunCNF.TraceRepresents b (rowBase np x)
    (length (program (verifierMachine (np_verifier np)))) (windowWidth np (length x)) trace).
  { eapply RunCNF.traceRepresents_congr; [|exact hrep]. intros v hv.
    unfold b, jointAssignment. rewrite (proj2 (Nat.ltb_ge _ _) hv). reflexivity. }
  assert (hi : RowRepresents b (rowBase np x) (length (program (verifierMachine (np_verifier np))))
    (windowWidth np (length x)) (initialRow np x b)).
  { destruct trace as [|c rest]; [contradiction|]. cbn [hd_error] in hh.
    injection hh as hh. change (c = initialRow np x a) in hh.
    assert (hid : initialRow np x b = initialRow np x a) by (unfold initialRow; rewrite hd; reflexivity).
    rewrite hid, <- hh. exact (proj1 hjrep). }
  exists b. split.
  - apply tableauCNF_unfold. split; [exact hcert|]. split.
    + apply (proj2 (initialCNF_row np x b hcert)). exact hi.
    + eapply RunCNF.runCNF_complete; eauto.
  - split; [exact hd|]. apply RunCNF.decodeTrace_represents; assumption.
Qed.
Theorem tableauCNF_iff : forall np x, Satisfiable (tableauCNF np x) <-> np_language np x = true.
Proof.
  intros np x. split.
  - intros [a hf]. apply (proj1 (windowVerifierTableau_iff_language np x)).
    exists a, (decodeTrace np x a). apply tableauCNF_sound. exact hf.
  - intro hx. destruct (proj2 (windowVerifierTableau_iff_language np x) hx) as [a [trace ht]].
    destruct (tableauCNF_complete np x a trace ht) as [b [hb _]]. exists b. exact hb.
Qed.
Theorem tableauCNF_rejecting_unsatisfiable : forall np x,
  (forall w, np_language np w = false) -> ~ Satisfiable (tableauCNF np x).
Proof. intros np x h. rewrite tableauCNF_iff, h. discriminate. Qed.
Theorem tableauCNF_overlong_rejected : forall np x cert a,
  evalPoly (np_certBound np) (length x) < length cert ->
  (forall v, v <= 2 * evalPoly (np_certBound np) (length x) -> a v = encodeCertificate cert v) ->
  evalCNF a (tableauCNF np x) = false.
Proof.
  intros np x cert a h he.
  assert (hc : evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = false).
  { rewrite (evalCNF_congr a (encodeCertificate cert) (rowBase np x)).
    - apply overlong_rejected. exact h.
    - intros v hv. apply he. unfold rowBase in hv. lia.
    - unfold rowBase. apply certificateCNF_variables. }
  unfold tableauCNF. rewrite !evalCNF_append, hc. reflexivity.
Qed.
Theorem tableauCNF_wrong_successor_rejected : forall np x a c d rest,
  step (verifierMachine (np_verifier np)) c <> inr d -> decodeTrace np x a = c :: d :: rest ->
  evalCNF a (tableauCNF np x) = false.
Proof.
  intros np x a c d rest hs hd.
  pose proof (RunCNF.runCNF_wrong_successor_rejected _ _ _ _ a c d rest hs hd) as h.
  unfold tableauCNF. rewrite !evalCNF_append, h, andb_false_r. reflexivity.
Qed.
Definition offsetPolynomial (np : ClassNP) : Polynomial :=
  polyAdd (polyMul {| coefficient := 2; degree := 0 |} (np_certBound np)) {| coefficient := 1; degree := 0 |}.
Definition sizePolynomial (np : ClassNP) : Polynomial :=
  polyAdd (certificatePolynomial (np_certBound np))
    (polyAdd (initialPolynomial (length (program (verifierMachine (np_verifier np))))
      (offsetPolynomial np) (windowPolynomial np))
      (RunCNF.runPolynomial (verifierMachine (np_verifier np))
        (offsetPolynomial np) (windowPolynomial np) (clockPolynomial np))).
Theorem encodeCNF_length_append : forall f g,
  length (encodeCNF (f ++ g)) = length (encodeCNF f) + length (encodeCNF g).
Proof. induction f; intros; cbn [encodeCNF app]; [reflexivity|]. rewrite !length_app, IHf. lia. Qed.
Theorem tableauCNF_encoded_size : forall np x,
  length (encodeCNF (tableauCNF np x)) <= evalPoly (sizePolynomial np) (length x).
Proof.
  intros np x.
  assert (hb : rowBase np x <= evalPoly (offsetPolynomial np) (length x)).
  { pose proof (polyAdd_eval (polyMul {| coefficient := 2; degree := 0 |} (np_certBound np))
      {| coefficient := 1; degree := 0 |} (length x)) as h.
    rewrite <- polyMul_eval in h. unfold rowBase, offsetPolynomial.
    unfold evalPoly at 1 3 in h. simpl in h. lia. }
  pose proof (windowWidth_polynomial np (length x)) as hw.
  pose proof (maxClock_polynomial np (length x)) as ht.
  pose proof (initialCNF_polynomial_size (length (program (verifierMachine (np_verifier np))))
    (offsetPolynomial np) (windowPolynomial np) (length x) (rowBase np x)
    (maxClock np (length x)) (evalPoly (np_certBound np) (length x)) (sources np x) hb
    ltac:(rewrite sources_length; exact hw)
    ltac:(rewrite sources_length; unfold windowWidth; lia)
    ltac:(unfold rowBase; lia) (windowSources_bound _ _ _ _ _)) as hi.
  pose proof (RunCNF.runCNF_polynomial_size (verifierMachine (np_verifier np))
    (offsetPolynomial np) (windowPolynomial np) (clockPolynomial np) (length x)
    (rowBase np x) (windowWidth np (length x)) (maxClock np (length x)) hb hw ht) as hr.
  pose proof (certificateCNF_polynomial_size (np_certBound np) (length x)) as hc.
  unfold tableauCNF, sizePolynomial. rewrite !encodeCNF_length_append.
  eapply Nat.le_trans; [|apply polyAdd_eval].
  rewrite <- Nat.add_assoc. apply Nat.add_le_mono; [exact hc|].
  eapply Nat.le_trans; [apply Nat.add_le_mono; eassumption|apply polyAdd_eval].
Qed.

End CookLevin.
