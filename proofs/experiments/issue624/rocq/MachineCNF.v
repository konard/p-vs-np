From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import LocalCNF.
Import ListNotations.

(** The shared instruction dispatch compiled to local CNF. Only state/symbol
    pairs are enumerated; tape movement and full tableaux remain separate. *)
Module MachineCNF.
Import Complexity Machines LocalCNF.

Definition Selected (a : Assignment) (base size value : nat) : Prop :=
  value < size /\ a (base + value) = true /\
    forall i, i < size -> a (base + i) = true -> i = value.

Theorem oneHot_selected : forall a base size,
  evalCNF a (oneHot base size) = true <-> exists v, Selected a base size v.
Proof. exact oneHot_models. Qed.

Definition lookupRules (first second out rows columns : nat)
  (f : nat -> nat -> nat) : CNF :=
  flat_map (fun i => map (fun j =>
    implies [mkLit (first + i) true; mkLit (second + j) true]
      [mkLit (out + f i j) true]) (seq 0 columns)) (seq 0 rows).

Theorem lookupRules_models : forall a first second out rows columns f,
  evalCNF a (lookupRules first second out rows columns f) = true <->
    forall i, i < rows -> forall j, j < columns ->
      a (first + i) = true -> a (second + j) = true -> a (out + f i j) = true.
Proof.
  intros a first second out rows columns f. unfold lookupRules.
  rewrite evalCNF_flatMap. split.
  - intros h i hi j hj hf hs.
    specialize (h i ltac:(apply in_seq; lia)). rewrite evalCNF_map in h.
    specialize (h j ltac:(apply in_seq; lia)). rewrite implies_models in h.
    assert (hc : evalClause a [mkLit (out + f i j) true] = true).
    { apply h. intros l [he|[he|[]]]; subst l; unfold evalLit; simpl;
        rewrite Bool.eqb_true_iff; assumption. }
    unfold evalClause, evalLit in hc. simpl in hc.
    rewrite orb_false_r, Bool.eqb_true_iff in hc. exact hc.
  - intros h i hi. apply in_seq in hi. rewrite evalCNF_map.
    intros j hj. apply in_seq in hj. rewrite implies_models.
    intro hp. assert (hf : a (first + i) = true).
    { specialize (hp (mkLit (first + i) true) (or_introl eq_refl)).
      unfold evalLit in hp. simpl in hp. rewrite Bool.eqb_true_iff in hp. exact hp. }
    assert (hs : a (second + j) = true).
    { specialize (hp (mkLit (second + j) true) (or_intror (or_introl eq_refl))).
      unfold evalLit in hp. simpl in hp. rewrite Bool.eqb_true_iff in hp. exact hp. }
    specialize (h i ltac:(lia) j ltac:(lia) hf hs).
    unfold evalClause, evalLit. simpl. rewrite h. reflexivity.
Qed.

Theorem lookupRules_selected : forall a first second out rows columns i j f,
  Selected a first rows i -> Selected a second columns j ->
  (evalCNF a (lookupRules first second out rows columns f) = true <->
    a (out + f i j) = true).
Proof.
  intros a first second out rows columns i j f [hi [hai hui]] [hj [haj huj]].
  rewrite lookupRules_models. split.
  - intro h. apply h; assumption.
  - intros h u hu v hv hau hav. rewrite (hui u hu hau), (huj v hv hav). exact h.
Qed.

Theorem lookupRules_length : forall first second out rows columns f,
  length (lookupRules first second out rows columns f) = rows * columns.
Proof.
  intros first second out rows columns f. unfold lookupRules.
  assert (h : forall xs : list nat, length (flat_map (fun i => map (fun j =>
    implies [mkLit (first + i) true; mkLit (second + j) true]
      [mkLit (out + f i j) true]) (seq 0 columns)) xs) = length xs * columns).
  { intro xs. induction xs; simpl; [reflexivity|].
    rewrite length_app, length_map, length_seq, IHxs. simpl. lia. }
  rewrite h, length_seq. reflexivity.
Qed.

Theorem lookupRules_bounds : forall first second out rows columns limit f,
  first + rows <= limit -> second + columns <= limit ->
  (forall i, i < rows -> forall j, j < columns -> out + f i j < limit) ->
  VarsBelow limit (lookupRules first second out rows columns f) /\
    forall c, In c (lookupRules first second out rows columns f) -> length c <= 3.
Proof.
  intros first second out rows columns limit f hf hs ho.
  assert (hc : forall c, In c (lookupRules first second out rows columns f) ->
    exists i j, i < rows /\ j < columns /\ c =
      implies [mkLit (first + i) true; mkLit (second + j) true] [mkLit (out + f i j) true]).
  { intros c h. unfold lookupRules in h. apply in_flat_map in h.
    destruct h as [i [hi h]]. apply in_map_iff in h.
    destruct h as [j [he hj]]. apply in_seq in hi, hj. exists i, j.
    split; [lia|]. split; [lia|]. symmetry. exact he. }
  split.
  - intros c h l hl. destruct (hc c h) as [i [j [hi [hj he]]]]. subst c.
    unfold implies, negate in hl. simpl in hl.
    destruct hl as [he|[he|[he|[]]]]; subst l; simpl; try lia. apply ho; assumption.
  - intros c h. destruct (hc c h) as [i [j [hi [hj he]]]]. subst c.
    unfold implies. simpl. lia.
Qed.

Definition symbols : list Symbol := [blank; zero; one; separator].
Definition symbolOfIndex (i : nat) : Symbol :=
  match i with 0 => blank | 1 => zero | 2 => one | _ => separator end.
Definition directionCode (d : Direction) : nat :=
  match d with left => 0 | right => 1 | stay => 2 end.
Definition instructionCode (i : Instruction) : nat :=
  match i with halt false => 0 | halt true => 1 |
    move q w d => 2 + 12 * q + 3 * symbolIndex w + directionCode d end.

Theorem instructionCode_injective : forall i j,
  instructionCode i = instructionCode j -> i = j.
Proof.
  intros [b|q w d] [b'|q' w' d'] h.
  - destruct b, b'; simpl in h; congruence.
  - destruct b, w', d'; cbn [instructionCode symbolIndex directionCode] in h; lia.
  - destruct b', w, d; cbn [instructionCode symbolIndex directionCode] in h; lia.
  - destruct w, w', d, d'; cbn [instructionCode symbolIndex directionCode] in h;
      try (assert (q = q') by lia; subst q'; reflexivity); lia.
Qed.

Theorem symbolOfIndex_index : forall s, symbolOfIndex (symbolIndex s) = s.
Proof. destruct s; reflexivity. Qed.
Theorem symbolIndex_lt : forall s, symbolIndex s < 4.
Proof. destruct s; simpl; lia. Qed.
Theorem symbolIndex_of_lt : forall i, i < 4 -> symbolIndex (symbolOfIndex i) = i.
Proof.
  intros [|[|[|[|i]]]] h; try reflexivity. lia.
Qed.

Definition instructionCodes (m : Machine) : list nat :=
  flat_map (fun q => map (fun s => instructionCode (instruction m q s)) symbols)
    (seq 0 (length (program m))).
Definition instructionBound (m : Machine) : nat :=
  fold_right Nat.max 0 (instructionCodes m) + 1.

Lemma le_foldMax : forall xs n, In n xs -> n <= fold_right Nat.max 0 xs.
Proof.
  intro xs. induction xs as [|x xs IH]; intros n h; [contradiction|].
  simpl in h. simpl. destruct h as [he|h].
  - subst n. apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact h|apply Nat.le_max_r].
Qed.

Theorem instructionCode_lt_bound : forall m q s, q < length (program m) ->
  instructionCode (instruction m q s) < instructionBound m.
Proof.
  intros m q s hq.
  assert (hs : In s symbols) by (destruct s; unfold symbols; simpl; auto).
  assert (hm : In (instructionCode (instruction m q s)) (instructionCodes m)).
  { unfold instructionCodes. apply in_flat_map. exists q. split; [apply in_seq; lia|].
    apply in_map_iff. exists s. split; [reflexivity|exact hs]. }
  pose proof (le_foldMax _ _ hm). unfold instructionBound. lia.
Qed.

Definition dispatchCNF (m : Machine) (base : nat) : CNF :=
  let states := length (program m) in
  let out := base + states + 4 in
  oneHot base states ++ oneHot (base + states) 4 ++ oneHot out (instructionBound m) ++
    lookupRules base (base + states) out states 4
      (fun q s => instructionCode (instruction m q (symbolOfIndex s))).

Theorem dispatchCNF_models : forall m base a,
  evalCNF a (dispatchCNF m base) = true <->
    exists q s, Selected a base (length (program m)) q /\
      Selected a (base + length (program m)) 4 (symbolIndex s) /\
      Selected a (base + length (program m) + 4) (instructionBound m)
        (instructionCode (instruction m q s)).
Proof.
  intros m base a. unfold dispatchCNF.
  repeat rewrite evalCNF_append. repeat rewrite andb_true_iff.
  repeat rewrite oneHot_selected. split.
  - intros [[q hq] [[s hs] [[v hv] hr]]].
    rewrite (lookupRules_selected _ _ _ _ _ _ q s _ hq hs) in hr.
    pose proof (instructionCode_lt_bound m q (symbolOfIndex s) (proj1 hq)) as hb.
    pose proof (proj2 (proj2 hv) _ hb hr) as he.
    exists q, (symbolOfIndex s). split; [exact hq|]. split.
    + rewrite symbolIndex_of_lt by exact (proj1 hs). exact hs.
    + rewrite he. exact hv.
  - intros [q [s [hq [hs ho]]]]. split; [exists q; exact hq|].
    split; [exists (symbolIndex s); exact hs|]. split; [eexists; exact ho|].
    rewrite (lookupRules_selected _ _ _ _ _ _ q (symbolIndex s) _ hq hs).
    rewrite symbolOfIndex_index. exact (proj1 (proj2 ho)).
Qed.

Definition dispatchAssignment (m : Machine) (base q : nat) (s : Symbol) : Assignment :=
  fun v => (v =? base + q) || (v =? base + length (program m) + symbolIndex s) ||
    (v =? base + length (program m) + 4 + instructionCode (instruction m q s)).

Theorem dispatchCNF_wrong_instruction : forall m base a q value s,
  Selected a base (length (program m)) q ->
  Selected a (base + length (program m)) 4 (symbolIndex s) ->
  Selected a (base + length (program m) + 4) (instructionBound m) value ->
  instructionCode (instruction m q s) <> value ->
  evalCNF a (dispatchCNF m base) = false.
Proof.
  intros m base a q value s hq hs ho hw.
  destruct (evalCNF a (dispatchCNF m base)) eqn:he; [|reflexivity].
  unfold dispatchCNF in he. repeat rewrite evalCNF_append in he.
  repeat rewrite andb_true_iff in he. destruct he as [_ [_ [_ hr]]].
  rewrite (lookupRules_selected _ _ _ _ _ _ q (symbolIndex s) _ hq hs) in hr.
  rewrite symbolOfIndex_index in hr.
  pose proof (instructionCode_lt_bound m q s (proj1 hq)) as hb.
  pose proof (proj2 (proj2 ho) _ hb hr) as hv. contradiction.
Qed.

Theorem dispatchAssignment_models : forall m base q s, q < length (program m) ->
  evalCNF (dispatchAssignment m base q s) (dispatchCNF m base) = true.
Proof.
  intros m base q s hq. pose proof (symbolIndex_lt s) as hs.
  pose proof (instructionCode_lt_bound m q s hq) as ho.
  apply dispatchCNF_models. exists q, s. unfold Selected.
  split.
  - split; [exact hq|]. split.
    + unfold dispatchAssignment. rewrite Nat.eqb_refl. reflexivity.
    + intros i hi h. unfold dispatchAssignment in h.
      repeat rewrite orb_true_iff in h. repeat rewrite Nat.eqb_eq in h.
      destruct h as [[h|h]|h]; lia.
  - split.
    + split; [exact hs|]. split.
      * unfold dispatchAssignment. rewrite Nat.eqb_refl, orb_true_r. reflexivity.
      * intros i hi h. unfold dispatchAssignment in h.
        repeat rewrite orb_true_iff in h. repeat rewrite Nat.eqb_eq in h.
        destruct h as [[h|h]|h]; lia.
    + split; [exact ho|]. split.
      * unfold dispatchAssignment. rewrite Nat.eqb_refl, orb_true_r. reflexivity.
      * intros i hi h. unfold dispatchAssignment in h.
        repeat rewrite orb_true_iff in h. repeat rewrite Nat.eqb_eq in h.
        destruct h as [[h|h]|h]; lia.
Qed.

Theorem dispatchCNF_instruction : forall m base a q s i,
  Selected a base (length (program m)) q ->
  Selected a (base + length (program m)) 4 (symbolIndex s) ->
  Selected a (base + length (program m) + 4) (instructionBound m) (instructionCode i) ->
  evalCNF a (dispatchCNF m base) = true -> instruction m q s = i.
Proof.
  intros m base a q s i hq hs ho hm. unfold dispatchCNF in hm.
  repeat rewrite evalCNF_append in hm. repeat rewrite andb_true_iff in hm.
  destruct hm as [_ [_ [_ hr]]].
  rewrite (lookupRules_selected _ _ _ _ _ _ q (symbolIndex s) _ hq hs) in hr.
  rewrite symbolOfIndex_index in hr.
  apply instructionCode_injective. apply (proj2 (proj2 ho)); [|exact hr].
  apply instructionCode_lt_bound. exact (proj1 hq).
Qed.

Theorem dispatchCNF_step : forall m base a c i,
  Selected a base (length (program m)) (state c) ->
  Selected a (base + length (program m)) 4 (symbolIndex (tapeHead c)) ->
  Selected a (base + length (program m) + 4) (instructionBound m) (instructionCode i) ->
  evalCNF a (dispatchCNF m base) = true ->
  step m c = match i with halt b => inl b |
    move q w d => inr (moveHead c q w d) end.
Proof.
  intros m base a c i hq hs ho hm. unfold step.
  rewrite (dispatchCNF_instruction m base a (state c) (tapeHead c) i hq hs ho hm).
  reflexivity.
Qed.

Theorem dispatchCNF_empty_unsatisfiable : forall base,
  ~ Satisfiable (dispatchCNF {| program := [] |} base).
Proof.
  intros base [a ha]. apply dispatchCNF_models in ha.
  destruct ha as [q [s [hq _]]]. unfold Selected in hq. simpl in hq. lia.
Qed.

Theorem dispatchCNF_encoded_size : forall m base,
  length (encodeCNF (dispatchCNF m base)) <=
    2 * (length (program m) * length (program m) + 4 * length (program m) +
      instructionBound m * instructionBound m + 19) *
      (1 + (length (program m) + instructionBound m + 7) *
        (base + length (program m) + instructionBound m + 5)).
Proof.
  intros m base.
  set (q := length (program m)). set (k := instructionBound m).
  set (limit := base + q + 4 + k). set (width := q + k + 7).
  destruct (oneHot_bounds base q) as [hv1 hw1].
  destruct (oneHot_bounds (base + q) 4) as [hv2 hw2].
  destruct (oneHot_bounds (base + q + 4) k) as [hv3 hw3].
  assert (hbound : forall i, i < q -> forall j, j < 4 ->
    base + q + 4 + instructionCode (instruction m i (symbolOfIndex j)) < limit).
  { intros i hi j hj. pose proof (instructionCode_lt_bound m i (symbolOfIndex j) hi).
    unfold limit, k. lia. }
  destruct (lookupRules_bounds base (base + q) (base + q + 4) q 4 limit
    (fun i j => instructionCode (instruction m i (symbolOfIndex j)))
    ltac:(unfold limit; lia) ltac:(unfold limit; lia) hbound) as [hv4 hw4].
  assert (hv : VarsBelow limit (dispatchCNF m base)).
  { intros c hc l hl. unfold dispatchCNF in hc. fold q k in hc.
    repeat rewrite in_app_iff in hc. destruct hc as [hc|[hc|[hc|hc]]].
    - specialize (hv1 c hc l hl). unfold limit. lia.
    - specialize (hv2 c hc l hl). unfold limit. lia.
    - exact (hv3 c hc l hl).
    - exact (hv4 c hc l hl). }
  assert (hw : forall c, In c (dispatchCNF m base) -> length c <= width).
  { intros c hc. unfold dispatchCNF in hc. fold q k in hc.
    repeat rewrite in_app_iff in hc. destruct hc as [hc|[hc|[hc|hc]]].
    - specialize (hw1 c hc). unfold width. lia.
    - specialize (hw2 c hc). unfold width. lia.
    - specialize (hw3 c hc). unfold width. lia.
    - specialize (hw4 c hc). unfold width. lia. }
  assert (hl : length (dispatchCNF m base) <= q * q + 4 * q + k * k + 19).
  { pose proof (oneHot_length base q). pose proof (oneHot_length (base + q) 4).
    pose proof (oneHot_length (base + q + 4) k).
    unfold dispatchCNF. fold q k. repeat rewrite length_app. rewrite lookupRules_length. lia. }
  pose proof (cnf_encoded_size _ _ _ hv hw) as h.
  eapply Nat.le_trans; [exact h|].
  unfold limit, width. fold q k. replace (base + q + 4 + k + 1) with (base + q + k + 5) by lia.
  apply Nat.mul_le_mono_r. lia.
Qed.

Definition dispatchPolynomial (m : Machine) (p : Polynomial) : Polynomial :=
  let q := length (program m) in
  let k := instructionBound m in
  let count := q * q + 4 * q + k * k + 19 in
  {| coefficient := 2 * count * (1 + (q + k + 7) * (coefficient p + q + k + 5));
     degree := degree p |}.

Theorem dispatchCNF_polynomial_size : forall m p n base,
  base <= evalPoly p n ->
  length (encodeCNF (dispatchCNF m base)) <= evalPoly (dispatchPolynomial m p) n.
Proof.
  intros m p n base hb.
  set (q := length (program m)). set (k := instructionBound m).
  assert (hp : 1 <= (n + 1) ^ degree p).
  { pose proof (Nat.pow_nonzero (n + 1) (degree p) ltac:(lia)). lia. }
  assert (hbase : base + q + k + 5 <= (coefficient p + q + k + 5) * (n + 1) ^ degree p).
  { unfold evalPoly in hb. nia. }
  assert (hcost : 1 + (q + k + 7) * (base + q + k + 5) <=
    (1 + (q + k + 7) * (coefficient p + q + k + 5)) * (n + 1) ^ degree p) by nia.
  eapply Nat.le_trans; [apply dispatchCNF_encoded_size|].
  unfold evalPoly, dispatchPolynomial. cbn [coefficient degree]. fold q k.
  rewrite <- (Nat.mul_assoc (2 * (q * q + 4 * q + k * k + 19))
    (1 + (q + k + 7) * (coefficient p + q + k + 5)) ((n + 1) ^ degree p)).
  apply Nat.mul_le_mono_l. exact hcost.
Qed.

End MachineCNF.
