From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import CertificateCNF VerifierTableau.
Import ListNotations Complexity.Complexity Machines CertificateCNF.
Import VerifierTableau.

Check certificateCNF_models.
Check decodeCertificate_length.
Check encodeCertificate_models.
Check decode_encodeCertificate.
Check encode_certificateCNF_length.
Check certificateCNF_polynomial_size.
Check certificateCNF_variables.
Check VerifierTableau.verifierTableau_iff_language.
Check VerifierTableau.verifierTableau_span.

Example empty_certificate : decodeCertificate (encodeCertificate []) 0 3 = [].
Proof. reflexivity. Qed.
Example short_false : decodeCertificate (encodeCertificate [false]) 0 3 = [false].
Proof. reflexivity. Qed.
Example short_mixed : decodeCertificate (encodeCertificate [true; false]) 0 3 = [true; false].
Proof. reflexivity. Qed.
Example zero_bound_length : length (encodeCNF (certificateCNF 0 0)) = 4.
Proof. reflexivity. Qed.
Example one_bound_length : length (encodeCNF (certificateCNF 0 1)) = 26.
Proof. reflexivity. Qed.
Example two_bound_length : length (encodeCNF (certificateCNF 0 2)) = 64.
Proof. reflexivity. Qed.
Example offset_bound_length : length (encodeCNF (certificateCNF 2 3)) = 222.
Proof. rewrite encode_certificateCNF_length. reflexivity. Qed.
Example hole_rejected : evalCNF (fun v => Nat.eqb v 2) (certificateCNF 0 2) = false.
Proof. reflexivity. Qed.
Example noncanonical_blank_rejected : evalCNF (fun v => Nat.eqb v 1) (certificateCNF 0 1) = false.
Proof. reflexivity. Qed.
Example overlong_rejected : evalCNF (encodeCertificate [true; false]) (certificateCNF 0 1) = false.
Proof. reflexivity. Qed.

Definition constantMachine (answer : bool) : Machine :=
  {| program := [[halt answer; halt answer; halt answer; halt answer]] |}.

Lemma constantRun : forall answer c, state c = 0 -> Run (constantMachine answer) c 1 answer.
Proof.
  intros answer c h. apply run_halt. unfold step. rewrite h.
  destruct (tapeHead c); reflexivity.
Qed.

Definition constantVerifier (isPaired answer : bool) : VerifierProgram :=
  if isPaired then paired (constantMachine answer) else ignoreCertificate (constantMachine answer).

Lemma constantVerifierRun : forall isPaired answer x cert,
  verifierRun (constantVerifier isPaired answer) x cert 1 answer.
Proof.
  intros [|] answer x cert; cbn [constantVerifier verifierRun];
    apply constantRun; destruct x; reflexivity.
Qed.

Lemma constantTime : forall isPaired answer x cert,
  timeLimit (constantVerifier isPaired answer) {| coefficient := 1; degree := 0 |} x cert = 1.
Proof. intros [|]; reflexivity. Qed.

Definition constantNP (isPaired answer : bool) (bound : nat) : ClassNP.
Proof.
  refine {| np_language := fun _ => answer;
            np_verifier := constantVerifier isPaired answer;
            np_timeBound := {| coefficient := 1; degree := 0 |};
            np_certBound := {| coefficient := bound; degree := 0 |} |}.
  - intros x cert _. exists 1, answer. split.
    + rewrite constantTime. reflexivity.
    + apply constantVerifierRun.
  - intro x. split.
    + intro h. exists [], 1. split; [simpl; apply Nat.le_0_l|].
      split; [rewrite constantTime; reflexivity|].
      rewrite <- h. apply constantVerifierRun.
    + intros [cert [t [_ [_ hr]]]].
      apply verifierRun_iff in hr.
      pose proof (constantVerifierRun isPaired answer x cert) as hc.
      apply verifierRun_iff in hc.
      pose proof (run_deterministic _ _ _ _ _ _ hr hc) as [_ hb]. symmetry. exact hb.
Defined.

Example paired_empty_model : VerifierTableau (constantNP true true 3) []
  (encodeCertificate []) [pairedInput [] []].
Proof. repeat split; reflexivity. Qed.
Example paired_short_model : VerifierTableau (constantNP true true 3) []
  (encodeCertificate [false]) [pairedInput [] [false]].
Proof. repeat split; reflexivity. Qed.
Example ignoring_model : VerifierTableau (constantNP false true 3) [true]
  (encodeCertificate [false]) [initial [true]].
Proof. repeat split; reflexivity. Qed.
Example paired_rejecting : forall x,
  ~ exists a trace, VerifierTableau (constantNP true false 3) x a trace.
Proof. intro x. apply rejecting_verifier_no_tableau. reflexivity. Qed.
Example ignoring_rejecting : forall x,
  ~ exists a trace, VerifierTableau (constantNP false false 3) x a trace.
Proof. intro x. apply rejecting_verifier_no_tableau. reflexivity. Qed.

Example empty_actual_clock : timeLimit (paired (constantMachine true))
  {| coefficient := 1; degree := 1 |} [] (decodeCertificate (encodeCertificate []) 0 3) = 2.
Proof. reflexivity. Qed.
Example short_actual_clock : timeLimit (paired (constantMachine true))
  {| coefficient := 1; degree := 1 |} [] (decodeCertificate (encodeCertificate [false]) 0 3) = 3.
Proof. reflexivity. Qed.
Example overlong_no_representation : ~ Represents (encodeCertificate [true; false]) 0 [true; false] 1.
Proof. apply overlong_not_representable. simpl. auto. Qed.
Example malformed_edge : ~ Tableau.Tableau.localTrace Tableau.Tableau.moveThenAccept true
  [initial []; Tableau.Tableau.wrongSuccessor].
Proof. exact Tableau.Tableau.wrong_successor_rejected. Qed.

Lemma emptyInputRun : forall x,
  exists t, t <= 2 /\ Run Tableau.Tableau.moveThenAccept (initial x) t
    (match x with [] => true | _ :: _ => false end).
Proof.
  intros [|b rest].
  - exists 2. split; [lia|].
    eapply run_next; [reflexivity|]. apply run_halt. reflexivity.
  - exists 1. split; [lia|]. apply run_halt. destruct b; reflexivity.
Qed.

Definition emptyInputNP : ClassNP.
Proof.
  refine {| np_language := fun x => match x with [] => true | _ :: _ => false end;
            np_verifier := ignoreCertificate Tableau.Tableau.moveThenAccept;
            np_timeBound := {| coefficient := 2; degree := 0 |};
            np_certBound := {| coefficient := 0; degree := 0 |} |}.
  - intros x cert _. destruct (emptyInputRun x) as [t [ht hr]].
    exists t, (match x with [] => true | _ :: _ => false end). split; assumption.
  - intro x. split.
    + intro hx. destruct (emptyInputRun x) as [t [ht hr]].
      exists [], t. split; [reflexivity|]. split; [exact ht|].
      rewrite hx in hr. exact hr.
    + intros [cert [t [_ [_ hr]]]].
      destruct (emptyInputRun x) as [u [_ hu]].
      pose proof (run_deterministic _ _ _ _ _ _ hr hu) as [_ hb]. symmetry. exact hb.
Defined.

Example good_successor_model : VerifierTableau emptyInputNP [] (encodeCertificate [])
  [initial []; Tableau.Tableau.goodSuccessor].
Proof. repeat split; reflexivity. Qed.
Example wrong_successor_nonmodel : ~ VerifierTableau emptyInputNP [] (encodeCertificate [])
  [initial []; Tableau.Tableau.wrongSuccessor].
Proof. apply wrong_successor_not_model. reflexivity. Qed.

Example accepting_run_exact_clock : forall np x cert t,
  length cert <= evalPoly (np_certBound np) (length x) ->
  verifierRun (np_verifier np) x cert t true ->
  t <= timeLimit (np_verifier np) (np_timeBound np) x cert.
Proof. apply acceptingRun_timeLimit. Qed.

Example rectangular_clock_exact : forall np x a trace,
  EnvelopeTableau np x a trace <-> VerifierTableau np x a trace.
Proof. apply envelopeTableau_iff_exact. Qed.

Print Assumptions certificateCNF_models.
Print Assumptions encodeCertificate_models.
Print Assumptions decode_encodeCertificate.
Print Assumptions certificateCNF_polynomial_size.
Print Assumptions encode_certificateCNF_length.
Print Assumptions certificateCNF_variables.
Print Assumptions CertificateCNF.overlong_rejected.
Print Assumptions VerifierTableau.verifierTableau_iff_language.
Print Assumptions VerifierTableau.maxClock_polynomial.
Print Assumptions VerifierTableau.verifierTableau_span.
Print Assumptions VerifierTableau.wrong_successor_not_model.

Print Assumptions VerifierTableau.acceptingRun_timeLimit.
Print Assumptions VerifierTableau.envelopeTableau_iff_exact.
Print Assumptions VerifierTableau.envelopeTableau_iff_language.
