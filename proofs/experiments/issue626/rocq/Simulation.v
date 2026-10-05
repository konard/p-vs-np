From Stdlib Require Import List Bool Arith Lia Ring.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue626.rocq Require Import NandCompiler Window.
From proofs.experiments.issue532.rocq Require Import CircuitModel.
Import ListNotations.

Module Simulation.
Import Complexity NandCompiler.

Definition symbolBit (s : Symbol) (lane : nat) : Expr :=
  lit (if lane =? 0 then 2 <=? symbolIndex s else symbolIndex s mod 2 =? 1).
Definition width (states cells : nat) : nat := 4 + states + 4 * cells.
Definition ref (r : list Expr) (i : nat) : Expr := nth i r (lit false).
Definition tapeRef (states cells : nat) (r : list Expr) (right : bool)
  (cell lane : nat) : Expr :=
  ref r (4 + states + (if right then 2 * cells else 0) + 2 * cell + lane).

Definition chooseSymbol (r : list Expr) (f : Symbol -> Expr) : Expr :=
  mux (ref r 2) (mux (ref r 3) (f separator) (f one))
    (mux (ref r 3) (f zero) (f blank)).

Fixpoint chooseState (m : Machine) (r : list Expr) (f : Instruction -> Expr)
    (q : nat) (rows : list (list Instruction)) : Expr :=
  match rows with
  | [] => f (halt false)
  | row :: rows => mux (ref r (4 + q))
      (chooseSymbol r (fun s => f (nth (symbolIndex s) row (halt false))))
      (chooseState m r f (q + 1) rows)
  end.

Definition movedBit (m : Machine) (cells : nat) (r : list Expr)
    (i q : nat) (s : Symbol) (d : Direction) : Expr :=
  if i =? 0 then lit false
  else if i =? 1 then lit false
  else if i <? 4 then
    match d with
    | stay => symbolBit s (i - 2)
    | left => tapeRef (length (program m)) cells r false 0 (i - 2)
    | right => tapeRef (length (program m)) cells r true 0 (i - 2)
    end
  else if i <? 4 + length (program m) then lit (i - 4 =? q)
  else
    let j := i - (4 + length (program m)) in
    let right := 2 * (cells - 1) <=? j in
    let off := if right then j - 2 * (cells - 1) else j in
    let cell := off / 2 in
    let lane := off mod 2 in
    match d, right with
    | stay, _ => tapeRef (length (program m)) cells r right cell lane
    | left, false | right, true =>
        tapeRef (length (program m)) cells r right (cell + 1) lane
    | right, false | left, true =>
        if cell =? 0 then symbolBit s lane
        else tapeRef (length (program m)) cells r right (cell - 1) lane
    end.

Definition instructionBit (m : Machine) (cells : nat) (r : list Expr)
    (i : nat) (instr : Instruction) : Expr :=
  match instr with
  | halt b => lit (if i =? 0 then true else if i =? 1 then b else false)
  | move q s d => movedBit m cells r i q s d
  end.

Definition stepExprs (m : Machine) (cells : nat) (r : list Expr) : list Expr :=
  map (fun i => mux (ref r 0)
    (if i =? 0 then lit true else if i =? 1 then ref r 1 else lit false)
    (chooseState m r (instructionBit m cells r i) 0 (program m)))
    (seq 0 (width (length (program m)) (cells - 1))).

Definition inputSymbolBit (n cell lane : nat) : Expr :=
  if cell <? n then if lane =? 0 then input cell else neg (input cell)
  else lit false.

Definition initialExprs (m : Machine) (n cells : nat) : list Expr :=
  map (fun i =>
    if i <? 2 then lit false
    else if i <? 4 then inputSymbolBit n 0 (i - 2)
    else if i <? 4 + length (program m) then lit (i =? 4)
    else let j := i - (4 + length (program m)) in
      if j <? 2 * cells then lit false
      else inputSymbolBit n ((j - 2 * cells) / 2 + 1) ((j - 2 * cells) mod 2))
    (seq 0 (width (length (program m)) cells)).

Definition finish (n : nat) (refs : list nat) : Circuit :=
  let a := nth 1 refs 0 in [(a,a); (n,n)].

Fixpoint compileRows (m : Machine) (t cells n : nat) (refs : list nat) : Circuit :=
  match t with
  | 0 => finish n refs
  | S t => let '(A,js) := compileMany n (stepExprs m cells (map input refs)) in
      A ++ compileRows m t (cells - 1) (n + length A) js
  end.

(** Only finite machine data, a polynomial clock, and input length are used.
    Input words and their precomputed answers are never compiler arguments. *)
Definition simCircuit (m : Machine) (p : Polynomial) (n : nat) : Circuit :=
  let clock := evalPoly p n in
  let cells := n + clock + 1 in
  let '(A,js) := compileMany n (initialExprs m n cells) in
  A ++ compileRows m clock cells (n + length A) js.

Lemma ref_bounded : forall r n, (forall e, In e r -> Bounded n e) ->
  forall i, Bounded n (ref r i).
Proof.
  induction r as [|e r IH]; intros n hr [|i]; simpl; try exact I.
  - apply hr. simpl. auto.
  - apply IH. intros a ha. apply hr. simpl. auto.
Qed.

Lemma mux_bounded : forall s a b n,
  Bounded n s -> Bounded n a -> Bounded n b -> Bounded n (mux s a b).
Proof. intros. unfold mux, neg. simpl. tauto. Qed.

Lemma chooseSymbol_bounded : forall r n f,
  (forall e, In e r -> Bounded n e) -> (forall s, Bounded n (f s)) ->
  Bounded n (chooseSymbol r f).
Proof.
  intros r n f hr hf. unfold chooseSymbol.
  repeat apply mux_bounded; try apply ref_bounded; auto.
Qed.

Lemma chooseState_bounded : forall m r n f,
  (forall e, In e r -> Bounded n e) -> (forall s, Bounded n (f s)) ->
  forall rows q, Bounded n (chooseState m r f q rows).
Proof.
  intros m r n f hr hf rows. induction rows; intros q; cbn [chooseState]; [apply hf|].
  apply mux_bounded; [apply ref_bounded; auto| |apply IHrows].
  apply chooseSymbol_bounded; auto.
Qed.

Lemma movedBit_bounded : forall m cells r n,
  (forall e, In e r -> Bounded n e) ->
  forall i q s d, Bounded n (movedBit m cells r i q s d).
Proof.
  intros m cells r n hr i q s d.
  assert (ht : forall side cell lane,
    Bounded n (tapeRef (length (program m)) cells r side cell lane))
    by (intros; apply ref_bounded; exact hr).
  unfold movedBit. destruct (i =? 0), (i =? 1), (i <? 4),
    (i <? 4 + length (program m)); try exact I.
  all: destruct d; try apply ht; try exact I.
  all: destruct (2 * (cells - 1) <=? i - (4 + length (program m)));
    try apply ht; try exact I.
  all: match goal with |- context [if ?b then _ else _] => destruct b end;
    first [exact I | apply ht].
Qed.

Lemma stepExprs_bounded : forall m cells r n,
  (forall e, In e r -> Bounded n e) ->
  forall e, In e (stepExprs m cells r) -> Bounded n e.
Proof.
  intros m cells r n hr e he. apply in_map_iff in he.
  destruct he as [i [<- hi]]. apply mux_bounded.
  - apply ref_bounded. exact hr.
  - destruct (i =? 0), (i =? 1); try exact I. apply ref_bounded. exact hr.
  - apply chooseState_bounded; [exact hr|]. intros [b|q s d];
      [exact I|apply movedBit_bounded; exact hr].
Qed.

Lemma inputSymbolBit_bounded : forall n cell lane, Bounded n (inputSymbolBit n cell lane).
Proof.
  intros. unfold inputSymbolBit. destruct (cell <? n) eqn:h; [|exact I].
  apply Nat.ltb_lt in h. destruct (lane =? 0); simpl; tauto.
Qed.

Lemma initialExprs_bounded : forall m n cells e,
  In e (initialExprs m n cells) -> Bounded n e.
Proof.
  intros m n cells e he. apply in_map_iff in he.
  destruct he as [i [<- hi]].
  destruct (i <? 2), (i <? 4), (i <? 4 + length (program m));
    try exact I; try apply inputSymbolBit_bounded.
  cbn zeta.
  destruct (i - (4 + length (program m)) <? 2 * cells);
    [exact I|apply inputSymbolBit_bounded].
Qed.

Lemma getD_lt : forall refs n, 0 < n -> (forall i, In i refs -> i < n) ->
  forall j, nth j refs 0 < n.
Proof.
  induction refs as [|i refs IH]; intros n hn hr [|j]; simpl; auto.
  - apply hr. simpl. auto.
  - apply IH; auto. intros a ha. apply hr. simpl. auto.
Qed.

Theorem compileRows_WF : forall m t cells n refs,
  0 < n -> (forall i, In i refs -> i < n) -> WFfrom n (compileRows m t cells n refs).
Proof.
  intros m t. induction t; intros cells n refs hn hr; cbn [compileRows].
  - unfold finish. simpl. pose proof (getD_lt refs n hn hr 1). intuition lia.
  - assert (he : forall e, In e (map input refs) -> Bounded n e).
    { intros e he. apply in_map_iff in he. destruct he as [i [<- hi]]. apply hr. exact hi. }
    pose proof (compileMany_WF (stepExprs m cells (map input refs)) n hn
      (stepExprs_bounded m cells (map input refs) n he)) as h.
    destruct (compileMany n (stepExprs m cells (map input refs))) as [A js]. simpl in h.
    destruct h as [hw hj]. apply WFfrom_append. split; [exact hw|apply IHt; auto; lia].
Qed.

Theorem simCircuit_WF : forall m p n, 0 < n -> WF n (simCircuit m p n).
Proof.
  intros m p n hn. unfold simCircuit, WF.
  pose proof (compileMany_WF (initialExprs m n (n + evalPoly p n + 1)) n hn
    (initialExprs_bounded m n (n + evalPoly p n + 1))) as h.
  destruct (compileMany n (initialExprs m n (n + evalPoly p n + 1))) as [A js].
  simpl in h. destruct h as [hw hj]. apply WFfrom_append.
  split; [exact hw|apply compileRows_WF; auto; lia].
Qed.

Lemma lit_cost_le : forall b, cost (lit b) <= 3.
Proof. intros []; simpl; lia. Qed.

Lemma ref_cost_le : forall r, (forall e, In e r -> cost e <= 3) ->
  forall i, cost (ref r i) <= 3.
Proof.
  induction r as [|e r IH]; intros hr [|i]; simpl; try lia.
  - apply hr. simpl. auto.
  - apply IH. intros a ha. apply hr. simpl. auto.
Qed.

Lemma mux_cost : forall s a b,
  cost (mux s a b) = 3 * cost s + cost a + cost b + 4.
Proof. intros. unfold mux, neg. simpl. lia. Qed.

Lemma chooseSymbol_cost : forall r f,
  (forall e, In e r -> cost e <= 3) -> (forall s, cost (f s) <= 3) ->
  cost (chooseSymbol r f) <= 51.
Proof.
  intros r f hr hf. unfold chooseSymbol. rewrite !mux_cost.
  pose proof (ref_cost_le r hr 2). pose proof (ref_cost_le r hr 3).
  pose proof (hf separator). pose proof (hf one). pose proof (hf zero). pose proof (hf blank).
  lia.
Qed.

Lemma chooseState_cost : forall m r f,
  (forall e, In e r -> cost e <= 3) -> (forall s, cost (f s) <= 3) ->
  forall rows q, cost (chooseState m r f q rows) <= 64 * length rows + 3.
Proof.
  intros m r f hr hf rows. induction rows as [|row rows IH]; intros q;
    cbn [chooseState length]; [apply hf|].
  rewrite mux_cost.
  pose proof (IH (q + 1)). pose proof (ref_cost_le r hr (4 + q)).
  pose proof (chooseSymbol_cost r (fun s => f (nth (symbolIndex s) row (halt false))) hr
    (fun s => hf _)). lia.
Qed.

Lemma movedBit_cost : forall m cells r,
  (forall e, In e r -> cost e <= 3) ->
  forall i q s d, cost (movedBit m cells r i q s d) <= 3.
Proof.
  intros m cells r hr i q s d.
  assert (ht : forall side cell lane,
    cost (tapeRef (length (program m)) cells r side cell lane) <= 3)
    by (intros; apply ref_cost_le; exact hr).
  assert (hs : forall lane, cost (symbolBit s lane) <= 3) by (intro; apply lit_cost_le).
  unfold movedBit. destruct (i =? 0), (i =? 1), (i <? 4),
    (i <? 4 + length (program m)); try apply lit_cost_le.
  all: destruct d; try apply ht; try apply hs.
  all: destruct (2 * (cells - 1) <=? i - (4 + length (program m))); try apply ht.
  all: match goal with |- context [if ?b then _ else _] => destruct b end;
    first [apply hs | apply ht].
Qed.

Definition rowCost (m : Machine) : nat := 64 * length (program m) + 19.

Lemma stepExprs_cost : forall m cells r,
  (forall e, In e r -> cost e <= 3) ->
  forall e, In e (stepExprs m cells r) -> cost e <= rowCost m.
Proof.
  intros m cells r hr e he. apply in_map_iff in he. destruct he as [i [<- hi]].
  assert (hf : forall instr, cost (instructionBit m cells r i instr) <= 3).
  { intros [b|q s d]; [apply lit_cost_le|apply movedBit_cost; exact hr]. }
  pose proof (chooseState_cost m r (instructionBit m cells r i) hr hf (program m) 0).
  pose proof (ref_cost_le r hr 0).
  assert (hh : cost (if i =? 0 then lit true else if i =? 1 then ref r 1 else lit false) <= 3).
  { destruct (i =? 0), (i =? 1); try apply lit_cost_le. apply ref_cost_le. exact hr. }
  rewrite mux_cost. unfold rowCost. lia.
Qed.

Lemma initialExprs_cost : forall m n cells e, In e (initialExprs m n cells) -> cost e <= 3.
Proof.
  intros m n cells e he.
  assert (hi : forall cell lane, cost (inputSymbolBit n cell lane) <= 3).
  { intros. unfold inputSymbolBit. destruct (cell <? n), (lane =? 0); simpl; lia. }
  apply in_map_iff in he. destruct he as [i [<- hin]].
  destruct (i <? 2), (i <? 4), (i <? 4 + length (program m));
    try apply lit_cost_le; try apply hi.
  cbn zeta.
  destruct (i - (4 + length (program m)) <? 2 * cells); [apply lit_cost_le|apply hi].
Qed.

Lemma totalCost_le : forall es k, (forall e, In e es -> cost e <= k) ->
  totalCost es <= k * length es.
Proof.
  induction es as [|e es IH]; intros k he.
  - change (0 <= k * 0). lia.
  - change (cost e + totalCost es <= k * S (length es)).
  assert (hs : forall a, In a es -> cost a <= k) by (intros; apply he; simpl; auto).
  pose proof (IH k hs). pose proof (he e (or_introl eq_refl)).
  change (cost e + totalCost es <= k * S (length es)). nia.
Qed.

Theorem compileRows_length : forall m t cells n refs,
  length (compileRows m t cells n refs) <= t * (rowCost m * width (length (program m)) cells) + 2.
Proof.
  intros m t. induction t; intros cells n refs; cbn [compileRows]; [unfold finish; simpl; lia|].
  assert (hr : forall e, In e (map input refs) -> cost e <= 3).
  { intros e he. apply in_map_iff in he. destruct he as [i [<- hi]]. simpl. lia. }
  pose proof (totalCost_le (stepExprs m cells (map input refs)) (rowCost m)
    (stepExprs_cost m cells (map input refs) hr)) as ha.
  unfold stepExprs in ha. rewrite length_map, length_seq in ha.
  pose proof (compileMany_cost (stepExprs m cells (map input refs)) n) as hc.
  destruct (compileMany n (stepExprs m cells (map input refs))) as [A js] eqn:he.
  cbn [fst] in hc. rewrite length_app.
  pose proof (IHt (cells - 1) (n + length A) js) as hb.
  assert (hw : width (length (program m)) (cells - 1) <= width (length (program m)) cells)
    by (unfold width; lia).
  fold (stepExprs m cells (map input refs)) in ha. rewrite <- hc in ha.
  set (a := rowCost m * width (length (program m)) (cells - 1)) in *.
  set (b := rowCost m * width (length (program m)) cells) in *.
  assert (hab : a <= b) by (unfold a,b; apply Nat.mul_le_mono; lia).
  pose proof (Nat.mul_le_mono (S t) (S t) a b ltac:(lia) hab). nia.
Qed.

Theorem simCircuit_length : forall m p n,
  length (simCircuit m p n) <=
    (evalPoly p n * rowCost m + 3) * width (length (program m)) (n + evalPoly p n + 1) + 2.
Proof.
  intros m p n. unfold simCircuit.
  pose proof (totalCost_le (initialExprs m n (n + evalPoly p n + 1)) 3
    (initialExprs_cost m n (n + evalPoly p n + 1))) as ha.
  pose proof (compileMany_cost (initialExprs m n (n + evalPoly p n + 1)) n) as hc.
  destruct (compileMany n (initialExprs m n (n + evalPoly p n + 1))) as [A js]. cbn [fst] in hc.
  unfold initialExprs in ha. rewrite length_map, length_seq in ha.
  fold (initialExprs m n (n + evalPoly p n + 1)) in ha. rewrite <- hc in ha.
  rewrite length_app.
  pose proof (compileRows_length m (evalPoly p n) (n + evalPoly p n + 1) (n + length A) js).
  nia.
Qed.

Definition simulationPolynomial (m : Machine) (p : Polynomial) : Polynomial :=
  {| coefficient := (coefficient p * rowCost m + 3) *
       (length (program m) + 4 * coefficient p + 8) + 2;
     degree := 2 * degree p + 1 |}.

Theorem simCircuit_polynomial_size : forall m p n,
  length (simCircuit m p n) <= evalPoly (simulationPolynomial m p) n.
Proof.
  intros m p n.
  set (E := (n + 1) ^ (degree p + 1)). set (F := (n + 1) ^ degree p).
  assert (hE : 1 <= E) by (unfold E; pose proof (Nat.pow_nonzero (n+1) (degree p+1) ltac:(lia)); lia).
  assert (hF : 1 <= F) by (unfold F; pose proof (Nat.pow_nonzero (n+1) (degree p) ltac:(lia)); lia).
  assert (hnE : n + 1 <= E).
  { unfold E. pose proof (Nat.pow_le_mono_r (n+1) 1 (degree p+1) ltac:(lia) ltac:(lia)).
    simpl in H. nia. }
  assert (hFE : F <= E) by (unfold F,E; apply Nat.pow_le_mono_r; lia).
  assert (hpE : evalPoly p n <= coefficient p * E) by (unfold evalPoly; fold F; nia).
  assert (hk : n + evalPoly p n + 1 <= (coefficient p + 1) * E) by nia.
  assert (hw : width (length (program m)) (n + evalPoly p n + 1) <=
    (length (program m) + 4 * coefficient p + 8) * E) by (unfold width; nia).
  assert (hcc : evalPoly p n * rowCost m + 3 <= (coefficient p * rowCost m + 3) * F)
    by (unfold evalPoly; fold F; nia).
  assert (hpow : F * E = (n + 1)^(2 * degree p + 1)).
  { unfold F,E. rewrite <- Nat.pow_add_r. f_equal. lia. }
  pose proof (simCircuit_length m p n) as hb.
  pose proof (Nat.mul_le_mono _ _ _ _ hcc hw) as hh.
  replace (((coefficient p * rowCost m + 3) * F) *
    ((length (program m) + 4 * coefficient p + 8) * E)) with
    (((coefficient p * rowCost m + 3) * (length (program m) + 4 * coefficient p + 8)) *
      (F * E)) in hh by ring.
  rewrite hpow in hh.
  assert (h2 : 1 <= (n + 1)^(2 * degree p + 1)) by (rewrite <- hpow; nia).
  change (length (simCircuit m p n) <=
    ((coefficient p * rowCost m + 3) * (length (program m) + 4 * coefficient p + 8) + 2) *
    (n + 1)^(2 * degree p + 1)).
  rewrite Nat.mul_add_distr_r. lia.
Qed.

End Simulation.
