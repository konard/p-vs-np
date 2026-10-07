From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
Import ListNotations.

(** The variable-length certificate fragment, not the full transition CNF.
    Presence is suffix-closed, absent cells have value false, and a forced
    blank sentinel excludes certificates longer than the bound. *)
Module CertificateCNF.
Import Complexity Machines.

Fixpoint certificateCNF (start bound : nat) : CNF :=
  match bound with
  | 0 => [[mkLit (2 * start) false]]
  | S n =>
      [mkLit (2 * start + 1) false; mkLit (2 * start) true] ::
      [mkLit (2 * (start + 1)) false; mkLit (2 * start) true] ::
      certificateCNF (start + 1) n
  end.

Fixpoint Represents (a : Assignment) (start : nat) (cert : Word) (bound : nat) : Prop :=
  match bound, cert with
  | 0, [] => a (2 * start) = false
  | 0, _ :: _ => False
  | S n, [] => a (2 * start) = false /\ a (2 * start + 1) = false /\
      Represents a (start + 1) [] n
  | S n, b :: rest => a (2 * start) = true /\ a (2 * start + 1) = b /\
      Represents a (start + 1) rest n
  end.

Fixpoint decodeCertificate (a : Assignment) (start bound : nat) : Word :=
  match bound with
  | 0 => []
  | S n => if a (2 * start) then
      a (2 * start + 1) :: decodeCertificate a (start + 1) n else []
  end.

Fixpoint encodeCertificate (cert : Word) (v : nat) {struct cert} : bool :=
  match cert with
  | [] => false
  | b :: rest => match v with
      | 0 => true
      | 1 => b
      | S (S v') => encodeCertificate rest v'
      end
  end.

Theorem decodeCertificate_length : forall a start bound,
  length (decodeCertificate a start bound) <= bound.
Proof.
  intros a start bound. revert start. induction bound; intro start; cbn [decodeCertificate].
  - simpl. lia.
  - destruct (a (2 * start)); simpl length; [specialize (IHbound (start + 1))|]; lia.
Qed.

Theorem represents_length : forall a start cert bound,
  Represents a start cert bound -> length cert <= bound.
Proof.
  intros a start cert bound. revert start cert.
  induction bound; intros start [|b cert] h; simpl in *; try contradiction; try lia.
  specialize (IHbound (start + 1) cert (proj2 (proj2 h))). lia.
Qed.

Theorem represents_decode : forall a start cert bound,
  Represents a start cert bound -> decodeCertificate a start bound = cert.
Proof.
  intros a start cert bound. revert start cert.
  induction bound; intros start [|b cert] h; cbn [Represents decodeCertificate] in *;
    try contradiction; try reflexivity.
  - destruct h as [hp [hb ht]]. rewrite hp. reflexivity.
  - destruct h as [hp [hb ht]]. rewrite hp, hb, (IHbound (start + 1) cert ht).
    reflexivity.
Qed.

Lemma represents_present : forall a start cert bound,
  Represents a start cert bound ->
  a (2 * start) = match cert with [] => false | _ :: _ => true end.
Proof.
  intros a start cert bound h. destruct bound, cert; simpl in *; tauto.
Qed.

Lemma certificateCNF_step : forall a start n,
  evalCNF a (certificateCNF start (S n)) = true <->
  (a (2 * start + 1) = false \/ a (2 * start) = true) /\
  (a (2 * (start + 1)) = false \/ a (2 * start) = true) /\
  evalCNF a (certificateCNF (start + 1) n) = true.
Proof.
  intros a start n. cbn [certificateCNF evalCNF evalClause evalLit var pos].
  unfold evalLit. cbn [var pos].
  destruct (a (2 * start + 1)), (a (2 * start)), (a (2 * (start + 1))),
    (evalCNF a (certificateCNF (start + 1) n)); simpl; intuition congruence.
Qed.

Lemma blank_of_model : forall a start bound,
  evalCNF a (certificateCNF start bound) = true -> a (2 * start) = false ->
  Represents a start [] bound.
Proof.
  intros a start bound. revert start. induction bound; intros start h hp.
  - exact hp.
  - apply certificateCNF_step in h. destruct h as [[hb|hp'] [[hn|hp''] ht]];
      try congruence.
    cbn [Represents]. split; [exact hp|]. split; [exact hb|].
    apply IHbound; assumption.
Qed.

(** A statement about each model, not only equisatisfiability. *)
Theorem certificateCNF_models : forall a start bound,
  evalCNF a (certificateCNF start bound) = true <->
  Represents a start (decodeCertificate a start bound) bound.
Proof.
  intros a start bound. revert start. induction bound; intro start.
  - cbn [certificateCNF evalCNF evalClause evalLit var pos decodeCertificate Represents].
    unfold evalLit. cbn [var pos].
    destruct (a (2 * start)); simpl; intuition congruence.
  - split; intro h; destruct (a (2 * start)) eqn:hp.
    + apply certificateCNF_step in h. destruct h as [_ [_ ht]].
      cbn [decodeCertificate]. rewrite hp. cbn [Represents].
      repeat split; auto. apply IHbound. exact ht.
    + cbn [decodeCertificate]. rewrite hp. apply blank_of_model; assumption.
    + cbn [decodeCertificate] in h. rewrite hp in h. cbn [Represents] in h.
      apply certificateCNF_step. split; [right; exact hp|].
      split; [right; exact hp|]. apply IHbound. tauto.
    + cbn [decodeCertificate] in h. rewrite hp in h. cbn [Represents] in h.
      destruct h as [_ [hb ht]].
      pose proof (represents_present a (start + 1) [] bound ht) as hn.
      apply certificateCNF_step. split; [left; exact hb|].
      split; [left; exact hn|]. apply IHbound.
      rewrite (represents_decode a (start + 1) [] bound ht). exact ht.
Qed.

Lemma represents_shift : forall bound a off cert start,
  Represents (fun v => a (v + 2 * off)) start cert bound <->
  Represents a (start + off) cert bound.
Proof.
  induction bound; intros a off cert start; destruct cert; cbn [Represents].
  - replace (2 * start + 2 * off) with (2 * (start + off)) by lia. reflexivity.
  - reflexivity.
  - replace (2 * start + 2 * off) with (2 * (start + off)) by lia.
    replace (2 * start + 1 + 2 * off) with (2 * (start + off) + 1) by lia.
    rewrite IHbound. replace (start + 1 + off) with (start + off + 1) by lia.
    reflexivity.
  - replace (2 * start + 2 * off) with (2 * (start + off)) by lia.
    replace (2 * start + 1 + 2 * off) with (2 * (start + off) + 1) by lia.
    rewrite IHbound. replace (start + 1 + off) with (start + off + 1) by lia.
    reflexivity.
Qed.

Lemma represents_congr : forall bound a b start cert,
  (forall v, a v = b v) -> Represents a start cert bound -> Represents b start cert bound.
Proof.
  induction bound; intros a b start cert he h; destruct cert; cbn [Represents] in *.
  - rewrite <- he. exact h.
  - contradiction.
  - destruct h as [hp [hb ht]]. rewrite <- (he (2 * start)), <- (he (2 * start + 1)).
    repeat split; auto. apply (IHbound a b (start + 1) [] he ht).
  - destruct h as [hp [hb ht]]. rewrite <- (he (2 * start)), <- (he (2 * start + 1)).
    repeat split; auto. apply (IHbound a b (start + 1) cert he ht).
Qed.

Lemma encodeCertificate_represents : forall bound cert,
  length cert <= bound -> Represents (encodeCertificate cert) 0 cert bound.
Proof.
  induction bound; intros cert h.
  - destruct cert; simpl in *; [reflexivity|lia].
  - destruct cert as [|b cert]; cbn [Represents encodeCertificate].
    + repeat split; try reflexivity.
      apply (proj1 (represents_shift bound (encodeCertificate []) 1 [] 0)).
      change (Represents (fun _ => false) 0 [] bound).
      specialize (IHbound [] (Nat.le_0_l bound)).
      cbn [encodeCertificate] in IHbound. exact IHbound.
    + repeat split; try reflexivity.
      apply (proj1 (represents_shift bound (encodeCertificate (b :: cert)) 1 cert 0)).
      apply (represents_congr bound (encodeCertificate cert)).
      * intro v. replace (v + 2 * 1) with (S (S v)) by lia. reflexivity.
      * apply IHbound. simpl in h. lia.
Qed.

Theorem encodeCertificate_models : forall cert bound,
  length cert <= bound -> evalCNF (encodeCertificate cert) (certificateCNF 0 bound) = true.
Proof.
  intros cert bound h. pose proof (encodeCertificate_represents bound cert h) as hr.
  apply certificateCNF_models. rewrite (represents_decode _ _ _ _ hr). exact hr.
Qed.

Theorem decode_encodeCertificate : forall cert bound,
  length cert <= bound -> decodeCertificate (encodeCertificate cert) 0 bound = cert.
Proof.
  intros cert bound h. apply represents_decode. apply encodeCertificate_represents. exact h.
Qed.

Theorem certificateCNF_variables : forall start bound,
  VarsBelow (2 * (start + bound) + 1) (certificateCNF start bound).
Proof.
  intros start bound. revert start. induction bound; intros start c hc l hl.
  - cbn [certificateCNF] in hc. destruct hc as [hc|[]]. subst c.
    destruct hl as [hl|[]]. subst l. cbn [var]. lia.
  - cbn [certificateCNF] in hc. destruct hc as [hc|[hc|hc]].
    + subst c. destruct hl as [hl|[hl|[]]]; subst l; cbn [var]; lia.
    + subst c. destruct hl as [hl|[hl|[]]]; subst l; cbn [var]; lia.
    + specialize (IHbound (start + 1) c hc l hl). lia.
Qed.

Theorem represents_sentinel : forall bound a start cert,
  Represents a start cert bound -> a (2 * (start + bound)) = false.
Proof.
  induction bound; intros a start cert h; destruct cert; cbn [Represents] in h.
  - replace (start + 0) with start by lia. exact h.
  - contradiction.
  - replace (start + S bound) with (start + 1 + bound) by lia.
    apply (IHbound a (start + 1) [] (proj2 (proj2 h))).
  - replace (start + S bound) with (start + 1 + bound) by lia.
    apply (IHbound a (start + 1) cert (proj2 (proj2 h))).
Qed.

Lemma encodeCertificate_present : forall cert i,
  i < length cert -> encodeCertificate cert (2 * i) = true.
Proof.
  induction cert as [|b cert IH]; intros [|i] h; simpl in h; try lia.
  - reflexivity.
  - replace (2 * S i) with (S (S (2 * i))) by lia.
    cbn [encodeCertificate]. apply IH. lia.
Qed.

Theorem overlong_rejected : forall cert bound,
  bound < length cert -> evalCNF (encodeCertificate cert) (certificateCNF 0 bound) = false.
Proof.
  intros cert bound h.
  destruct (evalCNF (encodeCertificate cert) (certificateCNF 0 bound)) eqn:he;
    [|reflexivity].
  apply certificateCNF_models in he.
  pose proof (represents_sentinel bound _ _ _ he) as hs.
  replace (0 + bound) with bound in hs by lia.
  rewrite (encodeCertificate_present cert bound h) in hs. discriminate.
Qed.

(** Retain the module's existing names while sharing the encoding proofs. *)
Lemma ticks_length : forall n, length (ticks n) = 2 * n.
Proof. exact Machines.ticks_length. Qed.

Lemma encodeLit_length : forall l, length (encodeLit l) = 2 * var l + 2.
Proof. exact Machines.encodeLit_length. Qed.

(** Count the unary variable identifiers, literal tokens, and delimiters. *)
Theorem encode_certificateCNF_length : forall start bound,
  length (encodeCNF (certificateCNF start bound)) =
  8 * bound * bound + 14 * bound + 4 + (16 * bound + 4) * start.
Proof.
  intros start bound. revert start. induction bound; intro start;
    cbn [certificateCNF encodeCNF encodeClause];
    repeat rewrite length_app; repeat rewrite encodeLit_length; simpl var;
    [simpl; lia|rewrite IHbound; simpl length; nia].
Qed.

Definition certificatePolynomial (p : Polynomial) : Polynomial :=
  {| coefficient := 8 * coefficient p * coefficient p + 14 * coefficient p + 4;
     degree := 2 * degree p |}.

(** Only this fragment's size: it is not a bound for the full tableau. *)
Theorem certificateCNF_polynomial_size : forall p n,
  length (encodeCNF (certificateCNF 0 (evalPoly p n))) <= evalPoly (certificatePolynomial p) n.
Proof.
  intros p n. rewrite encode_certificateCNF_length.
  unfold certificatePolynomial, evalPoly. cbn [coefficient degree].
  assert (hpow : 1 <= (n + 1) ^ degree p).
  { induction (degree p); simpl; nia. }
  replace (2 * degree p) with (degree p + degree p) by lia.
  rewrite Nat.pow_add_r. nia.
Qed.

End CertificateCNF.
