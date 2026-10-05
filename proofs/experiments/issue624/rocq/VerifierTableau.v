From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import CertificateCNF.
Import ListNotations.

(** A semantic interface to the existing local trace, not a full tableau CNF.
    The clock is evaluated at the decoded certificate's actual length. *)
Module VerifierTableau.
Import Complexity Machines Tableau CertificateCNF.

Definition verifierMachine (v : VerifierProgram) : Machine :=
  match v with ignoreCertificate m | paired m => m end.

Definition verifierInitial (v : VerifierProgram) (x cert : Word) : Config :=
  match v with
  | ignoreCertificate _ => initial x
  | paired _ => pairedInput x cert
  end.

Theorem verifierRun_iff : forall v x cert t b,
  verifierRun v x cert t b <-> Run (verifierMachine v) (verifierInitial v x cert) t b.
Proof. intros [m|m]; reflexivity. Qed.

Definition VerifierTableau (np : ClassNP) (x : Word) (a : Assignment)
    (trace : list Config) : Prop :=
  let cert := decodeCertificate a 0 (evalPoly (np_certBound np) (length x)) in
  evalCNF a (certificateCNF 0 (evalPoly (np_certBound np) (length x))) = true /\
  hd_error trace = Some (verifierInitial (np_verifier np) x cert) /\
  length trace <= timeLimit (np_verifier np) (np_timeBound np) x cert /\
  localTrace (verifierMachine (np_verifier np)) true trace.

(** Covers every ClassNP and both verifier constructors. *)
Theorem verifierTableau_iff_language : forall np x,
  (exists a trace, VerifierTableau np x a trace) <-> np_language np x = true.
Proof.
  intros np x. split.
  - intros [a [trace [_ [hhead [hclock hlocal]]]]]. apply (proj2 (np_correct np x)).
    exists (decodeCertificate a 0 (evalPoly (np_certBound np) (length x))), (length trace).
    split; [apply decodeCertificate_length|]. split; [exact hclock|].
    apply verifierRun_iff. apply (proj1 (localTrace_iff_run _ _ _ true)).
    exists trace. auto.
  - intro hx. destruct (proj1 (np_correct np x) hx)
      as [cert [t [hcert [htime hr]]]].
    apply verifierRun_iff in hr.
    destruct (proj2 (localTrace_iff_run _ _ t true) hr)
      as [trace [hhead [hlen hlocal]]].
    exists (encodeCertificate cert), trace. unfold VerifierTableau.
    rewrite (decode_encodeCertificate cert _ hcert).
    split; [apply encodeCertificate_models; exact hcert|].
    repeat split; auto. rewrite hlen. exact htime.
Qed.

Lemma polynomial_mono : forall p n k, n <= k -> evalPoly p n <= evalPoly p k.
Proof.
  intros p n k h. unfold evalPoly. apply Nat.mul_le_mono_l.
  apply Nat.pow_le_mono_l. lia.
Qed.

(** Only a sizing envelope. The acceptance predicate keeps its exact clock. *)
Definition maxClock (np : ClassNP) (n : nat) : nat :=
  evalPoly (np_timeBound np) (n + evalPoly (np_certBound np) n + 1).

Definition clockPolynomial (np : ClassNP) : Polynomial :=
  {| coefficient := coefficient (np_timeBound np) *
       (coefficient (np_certBound np) + 2) ^ degree (np_timeBound np);
     degree := (degree (np_certBound np) + 1) * degree (np_timeBound np) |}.

Theorem verifierTimeLimit_le : forall np x cert,
  length cert <= evalPoly (np_certBound np) (length x) ->
  timeLimit (np_verifier np) (np_timeBound np) x cert <= maxClock np (length x).
Proof.
  intros np x cert h. unfold maxClock. destruct (np_verifier np);
    cbn [timeLimit]; apply polynomial_mono; lia.
Qed.

Theorem maxClock_polynomial : forall np n,
  maxClock np n <= evalPoly (clockPolynomial np) n.
Proof.
  intros np n.
  assert (hpow : 1 <= (n + 1) ^ degree (np_certBound np)).
  { induction (degree (np_certBound np)); simpl; nia. }
  assert (hgrowth : n + 1 <= (n + 1) ^ (degree (np_certBound np) + 1)).
  { rewrite Nat.pow_add_r. simpl. nia. }
  assert (hold : (n + 1) ^ degree (np_certBound np) <=
      (n + 1) ^ (degree (np_certBound np) + 1)).
  { apply Nat.pow_le_mono_r; lia. }
  assert (hbase : n + evalPoly (np_certBound np) n + 1 + 1 <=
      (coefficient (np_certBound np) + 2) * (n + 1) ^ (degree (np_certBound np) + 1)).
  { unfold evalPoly. nia. }
  unfold maxClock, clockPolynomial, evalPoly. cbn [coefficient degree].
  rewrite Nat.pow_mul_r, <- Nat.mul_assoc, <- Nat.pow_mul_l.
  apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. exact hbase.
Qed.

Theorem verifierInitial_span : forall v x cert,
  span (verifierInitial v x cert) <= length x + length cert + 2.
Proof.
  intros [m|m] x cert.
  - change (span (initial x) <= length x + length cert + 2).
    pose proof (initial_span_le x). lia.
  - destruct x; unfold verifierInitial, pairedInput, initialSymbols, span;
      simpl; repeat rewrite length_app; repeat rewrite length_map;
      simpl; rewrite ?length_map; lia.
Qed.

(** A uniform tape-cell envelope; no full CNF size bound is claimed. *)
Theorem verifierTableau_span : forall np x a trace d,
  VerifierTableau np x a trace -> In d trace ->
  span d <= length x + evalPoly (np_certBound np) (length x) + maxClock np (length x) + 2.
Proof.
  intros np x a trace d [_ [hhead [htime hlocal]]] hd.
  pose proof (decodeCertificate_length a 0 (evalPoly (np_certBound np) (length x))) as hcert.
  pose proof (trace_span_bound _ true trace _ d hhead hlocal hd) as hspan.
  pose proof (verifierInitial_span (np_verifier np) x
    (decodeCertificate a 0 (evalPoly (np_certBound np) (length x)))) as hinit.
  pose proof (verifierTimeLimit_le np x _ hcert) as hclock. lia.
Qed.

Theorem overlong_not_representable : forall a cert bound,
  bound < length cert -> ~ Represents a 0 cert bound.
Proof. intros a cert bound h hr. pose proof (represents_length _ _ _ _ hr). lia. Qed.

Theorem rejecting_verifier_no_tableau : forall np x,
  np_language np x = false -> ~ exists a trace, VerifierTableau np x a trace.
Proof.
  intros np x h. rewrite verifierTableau_iff_language, h. discriminate.
Qed.

(** Reuse the malformed-edge counterexample, even though the last row accepts. *)
Theorem wrong_successor_not_model : forall np x a,
  verifierMachine (np_verifier np) = moveThenAccept ->
  ~ VerifierTableau np x a [initial []; wrongSuccessor].
Proof.
  intros np x a hm [_ [_ [_ hl]]]. rewrite hm in hl.
  exact (wrong_successor_rejected hl).
Qed.

End VerifierTableau.
