From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.
From proofs.experiments.issue624.rocq Require Import LocalCNF.
Import ListNotations Complexity Machines LocalCNF.

(** Tseitin compilation reuses the existing NAND circuit, wire indices, CNF,
    and unary encoding. Each gate contributes three clauses. *)
Module CircuitCNF.

Definition gateCNF (o i j : nat) : CNF :=
  [[mkLit o true; mkLit i true]; [mkLit o true; mkLit j true];
    [mkLit o false; mkLit i false; mkLit j false]].

Theorem gateCNF_models : forall a o i j,
  evalCNF a (gateCNF o i j) = true <-> a o = negb (andb (a i) (a j)).
Proof.
  intros a o i j. unfold gateCNF, evalCNF, evalClause, evalLit. simpl.
  destruct (a o), (a i), (a j); simpl; intuition congruence.
Qed.

Fixpoint circuitCNF (n : nat) (C : Circuit) : CNF :=
  match C with
  | [] => []
  | (i, j) :: C => gateCNF n i j ++ circuitCNF (n + 1) C
  end.

Definition Agrees (a : Assignment) (w : Word) : Prop :=
  forall i, i < length w -> a i = wire w i.

Theorem agrees_prefix : forall a w C, Agrees a (wires w C) -> Agrees a w.
Proof.
  intros a w C h i hi. rewrite <- (wire_wires_lt w C i hi).
  apply h. rewrite wires_length. lia.
Qed.

Theorem agrees_append : forall a w b,
  Agrees a (w ++ [b]) <-> Agrees a w /\ a (length w) = b.
Proof.
  intros a w b. split.
  - intro h. split.
    + intros i hi. rewrite <- (wire_append_lt w b i hi).
      apply h. rewrite length_app. simpl. lia.
    + rewrite <- (wire_append_self w b). apply h. rewrite length_app. simpl. lia.
  - intros [h hb] i hi. rewrite length_app in hi. simpl in hi.
    destruct (Nat.lt_ge_cases i (length w)) as [hit|hit].
    + rewrite wire_append_lt by exact hit. apply h. exact hit.
    + assert (he : i = length w) by lia. subst i. rewrite wire_append_self. exact hb.
Qed.

Theorem circuitCNF_models : forall a w C, WF (length w) C -> Agrees a w ->
  evalCNF a (circuitCNF (length w) C) = true <-> Agrees a (wires w C).
Proof.
  intros a w C. revert w. induction C as [|[i j] C IH]; intros w hw ha.
  - simpl. split; [intros _; exact ha|intros _; reflexivity].
  - destruct hw as [hi [hj ht]].
    set (b := negb (andb (wire w i) (wire w j))).
    assert (hb : evalCNF a (gateCNF (length w) i j) = true <-> a (length w) = b).
    { rewrite gateCNF_models, (ha i hi), (ha j hj). reflexivity. }
    assert (ht' : WF (length (w ++ [b])) C).
    { rewrite length_app. simpl. exact ht. }
    cbn [circuitCNF wires]. rewrite evalCNF_append, andb_true_iff, hb.
    change ((a (length w) = b /\ evalCNF a (circuitCNF (length w + 1) C) = true) <->
      Agrees a (wires (w ++ [b]) C)). split.
    + intros [hab hf]. assert (he : Agrees a (w ++ [b])) by (apply agrees_append; auto).
      apply (proj1 (IH _ ht' he)). rewrite length_app. simpl. exact hf.
    + intro he. pose proof (agrees_prefix _ _ _ he) as hp.
      split; [apply agrees_append in hp; tauto|].
      apply (proj2 (IH _ ht' hp)) in he. rewrite length_app in he. simpl in he. exact he.
Qed.

Definition acceptingCNF (n : nat) (C : Circuit) : CNF :=
  circuitCNF n C ++ if Nat.eqb (n + length C) 0 then [[]]
    else [[mkLit (n + length C - 1) true]].

Lemma lastD_wire : forall w : Word, last w false = wire w (length w - 1).
Proof.
  intro w. induction w as [|b w IH]; [reflexivity|].
  destruct w as [|c w]; [reflexivity|].
  cbn [last length] in *.
  unfold wire in *. replace (S (S (length w)) - 1) with (S (length w)) by lia.
  cbn [nth]. replace (S (length w) - 1) with (length w) in IH by lia. exact IH.
Qed.


Lemma prefix_agrees : forall a n, Agrees a (prefixOf a n).
Proof.
  intros a n i hi. rewrite length_prefixOf in hi.
  rewrite <- toAssign_wire. symmetry. apply toAssign_prefixOf. exact hi.
Qed.

Lemma output_of_agrees : forall a x C,
  Agrees a (wires x C) -> 0 < length x + length C ->
  output x C = a (length x + length C - 1).
Proof.
  intros a x C ha hp. unfold output. rewrite lastD_wire, wires_length.
  symmetry. apply ha. rewrite wires_length. lia.
Qed.

Theorem acceptingCNF_iff : forall n C, WF n C ->
  Satisfiable (acceptingCNF n C) <->
    exists x : Word, length x = n /\ output x C = true.
Proof.
  intros n C hw. split.
  - intros [a ha]. unfold acceptingCNF in ha. rewrite evalCNF_append, andb_true_iff in ha.
    destruct ha as [hc ho]. destruct (Nat.eqb (n + length C) 0) eqn:hz; [discriminate|].
    apply Nat.eqb_neq in hz. exists (prefixOf a n). split; [apply length_prefixOf|].
    assert (hwa : WF (length (prefixOf a n)) C) by (rewrite length_prefixOf; exact hw).
    pose proof (proj1 (circuitCNF_models a _ C hwa (prefix_agrees a n))) as he.
    rewrite length_prefixOf in he. specialize (he hc).
    rewrite (output_of_agrees a _ C he) by (rewrite length_prefixOf; lia).
    rewrite length_prefixOf. cbn [evalCNF evalClause evalLit var pos] in ho.
    rewrite orb_false_r, andb_true_r in ho.
    unfold evalLit in ho. cbn [var pos] in ho. rewrite Bool.eqb_true_iff in ho. exact ho.
  - intros [x [hx ho]]. set (a := toAssign (wires x C)).
    assert (he : Agrees a (wires x C)).
    { intros i _. unfold a. apply toAssign_wire. }
    pose proof (agrees_prefix _ _ _ he) as hp.
    assert (hwa : WF (length x) C) by (rewrite hx; exact hw).
    pose proof (proj2 (circuitCNF_models a x C hwa hp) he) as hc.
    assert (hz : n + length C <> 0).
    { intro hz. assert (hC : C = []) by (apply length_zero_iff_nil; lia).
      assert (hX : x = []) by (apply length_zero_iff_nil; lia).
      subst C x. discriminate. }
    exists a. unfold acceptingCNF. rewrite evalCNF_append, andb_true_iff.
    split; [rewrite <- hx; exact hc|].
    assert (hnz : Nat.eqb (n + length C) 0 = false) by (apply Nat.eqb_neq; exact hz).
    rewrite hnz. cbn [evalCNF evalClause evalLit var pos].
    assert (hab : a (n + length C - 1) = true).
    { rewrite <- hx, <- (output_of_agrees a x C he); [exact ho|lia]. }
    unfold evalLit. cbn [var pos]. rewrite hab. reflexivity.
Qed.

Lemma circuitCNF_length : forall n C, length (circuitCNF n C) = 3 * length C.
Proof.
  intros n C. revert n. induction C as [|[i j] C IH]; intro n; [reflexivity|].
  cbn [circuitCNF]. rewrite length_app, IH. cbn [gateCNF length]. lia.
Qed.

Lemma circuitCNF_bounds : forall n C, WF n C ->
  VarsBelow (n + length C) (circuitCNF n C) /\
    forall c, In c (circuitCNF n C) -> length c <= 3.
Proof.
  intros n C. revert n. induction C as [|[i j] C IH]; intros n hw.
  - cbn [circuitCNF]. split; [unfold VarsBelow|]; intros c hc; contradiction.
  - destruct hw as [hi [hj ht]].
    destruct (IH (n + 1) ht) as [hv hw']. split.
    + intros c hc l hl. cbn [circuitCNF] in hc. apply in_app_or in hc.
      destruct hc as [hc|hc].
      * cbn [gateCNF] in hc. destruct hc as [he|[he|[he|[]]]]; subst c;
          cbn in hl; intuition subst; cbn [var]; simpl length; lia.
      * pose proof (hv c hc l hl). simpl length. lia.
    + intros c hc. cbn [circuitCNF] in hc. apply in_app_or in hc.
      destruct hc as [hc|hc].
      * cbn [gateCNF] in hc. destruct hc as [he|[he|[he|[]]]]; subst c; cbn; lia.
      * apply hw'. exact hc.
Qed.

Theorem acceptingCNF_encoded_size : forall n C, WF n C ->
  length (encodeCNF (acceptingCNF n C)) <=
    8 * (3 * length C + 1) * (n + length C + 1).
Proof.
  intros n C hw. destruct (circuitCNF_bounds n C hw) as [hv hw'].
  assert (hvars : VarsBelow (n + length C) (acceptingCNF n C)).
  { intros c hc l hl. unfold acceptingCNF in hc. apply in_app_or in hc.
    destruct hc as [hc|hc]; [exact (hv c hc l hl)|].
    destruct (Nat.eqb (n + length C) 0) eqn:hz.
    - cbn in hc. destruct hc as [he|[]]. subst c. contradiction.
    - apply Nat.eqb_neq in hz. cbn in hc. destruct hc as [he|[]]. subst c.
      cbn in hl. destruct hl as [he|[]]. subst l. cbn [var]. lia. }
  assert (hwidth : forall c, In c (acceptingCNF n C) -> length c <= 3).
  { intros c hc. unfold acceptingCNF in hc. apply in_app_or in hc.
    destruct hc as [hc|hc]; [apply hw'; exact hc|].
    destruct (Nat.eqb (n + length C) 0); cbn in hc;
      destruct hc as [he|[]]; subst c; cbn; lia. }
  assert (hlen : length (acceptingCNF n C) = 3 * length C + 1).
  { unfold acceptingCNF. rewrite length_app, circuitCNF_length.
    destruct (Nat.eqb (n + length C) 0); reflexivity. }
  pose proof (cnf_encoded_size _ _ 3 hvars hwidth) as h. rewrite hlen in h.
  assert (ht : 1 + 3 * (n + length C + 1) <= 4 * (n + length C + 1)) by lia.
  eapply Nat.le_trans; [exact h|].
  replace (8 * (3 * length C + 1) * (n + length C + 1))
    with (2 * (3 * length C + 1) * (4 * (n + length C + 1))) by nia.
  apply Nat.mul_le_mono_l. exact ht.
Qed.

(** Unary wire identifiers square a polynomial bound on the wire count. *)
Definition circuitPolynomial (p : Polynomial) : Polynomial :=
  {| coefficient := 8 * (3 * coefficient p + 1) * (coefficient p + 1);
     degree := 2 * degree p |}.

Theorem acceptingCNF_polynomial_size : forall p inputLength n C,
  WF n C -> n + length C <= evalPoly p inputLength ->
  length (encodeCNF (acceptingCNF n C)) <=
    evalPoly (circuitPolynomial p) inputLength.
Proof.
  intros p inputLength n C hw hs.
  assert (hz : 1 <= (inputLength + 1) ^ degree p).
  { induction (degree p); simpl; nia. }
  assert (hl : 3 * length C + 1 <=
    (3 * coefficient p + 1) * (inputLength + 1) ^ degree p).
  { unfold evalPoly in hs. nia. }
  assert (hr : n + length C + 1 <=
    (coefficient p + 1) * (inputLength + 1) ^ degree p).
  { unfold evalPoly in hs. nia. }
  eapply Nat.le_trans; [apply acceptingCNF_encoded_size; exact hw|].
  unfold evalPoly, circuitPolynomial. cbn [coefficient degree].
  replace (2 * degree p) with (degree p + degree p) by lia.
  rewrite Nat.pow_add_r. nia.
Qed.

End CircuitCNF.
