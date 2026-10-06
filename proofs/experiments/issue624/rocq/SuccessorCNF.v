From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import LocalCNF MachineCNF FixedWindow.
Import ListNotations.

(** CNF for one charged move between finite tape rows. States, head positions,
    cells and four symbols are enumerated, never complete configurations. *)
Module SuccessorCNF.
Import Complexity Machines Tableau LocalCNF MachineCNF.

Definition flatten (c : Config) : list Symbol := rev (tapeLeft c) ++ tapeHead c :: tapeRight c.
Definition cell (c : Config) (i : nat) : Symbol := nth i (flatten c) blank.
Definition decodeConfig (q h : nat) (xs : list Symbol) : Config :=
  {| state := q; tapeLeft := rev (firstn h xs); tapeHead := nth h xs blank;
     tapeRight := skipn (h + 1) xs |}.

Theorem flatten_length : forall c, length (flatten c) = span c.
Proof. intros [q l a r]. unfold flatten, span. simpl. rewrite length_app, length_rev. simpl. lia. Qed.
Theorem cell_head : forall c, cell c (length (tapeLeft c)) = tapeHead c.
Proof.
  intros [q l a r]. unfold cell, flatten. simpl.
  replace (length l) with (length (rev l)) by apply length_rev.
  apply nth_middle.
Qed.
Theorem decodeConfig_flatten : forall c,
  decodeConfig (state c) (length (tapeLeft c)) (flatten c) = c.
Proof.
  intros [q l a r]. unfold decodeConfig, flatten. simpl.
  rewrite firstn_app, skipn_app, length_rev.
  rewrite Nat.sub_diag, firstn_all2 by (rewrite length_rev; lia).
  simpl firstn. rewrite app_nil_r, rev_involutive.
  rewrite skipn_all2 by (rewrite length_rev; lia).
  replace (length l + 1 - length l) with 1 by lia. simpl skipn. simpl app.
  replace (length l) with (length (rev l)) at 1 by apply length_rev.
  rewrite nth_middle. reflexivity.
Qed.
Theorem flatten_injective : forall c d, state c = state d ->
  length (tapeLeft c) = length (tapeLeft d) -> flatten c = flatten d -> c = d.
Proof.
  intros c d hq hh ht. rewrite <- (decodeConfig_flatten c), <- (decodeConfig_flatten d).
  rewrite hq, hh, ht. reflexivity.
Qed.

Fixpoint setCell (xs : list Symbol) (i : nat) (w : Symbol) : list Symbol :=
  match xs, i with [], _ => [] | _ :: rest, 0 => w :: rest |
    a :: rest, S j => a :: setCell rest j w end.
Lemma setCell_at_append : forall xs a ys w,
  setCell (xs ++ a :: ys) (length xs) w = xs ++ w :: ys.
Proof. induction xs; intros; simpl; [reflexivity|rewrite IHxs; reflexivity]. Qed.
Lemma setCell_length : forall xs i w, length (setCell xs i w) = length xs.
Proof. induction xs; intros [|i] w; simpl; auto. Qed.
Lemma setCell_nth : forall xs i j w, i < length xs -> j < length xs ->
  nth j (setCell xs i w) blank = if Nat.eq_dec j i then w else nth j xs blank.
Proof.
  induction xs as [|a xs IH]; intros [|i] [|j] w hi hj; simpl in *; try lia;
    try reflexivity.
  rewrite IH by lia. destruct (Nat.eq_dec j i); congruence.
Qed.

Definition nextHead (h : nat) (dir : Direction) : nat :=
  match dir with left => h - 1 | right => h + 1 | stay => h end.
Definition Inside (width h : nat) (dir : Direction) : Prop :=
  match dir with left => 0 < h | right => h + 1 < width | stay => True end.
Definition inside_dec (width h : nat) (dir : Direction) :
  {Inside width h dir} + {~ Inside width h dir}.
Proof. destruct dir; unfold Inside; [apply lt_dec|apply lt_dec|left; exact I]. Defined.
Definition moveAllowed_dec (states width target h : nat) (dir : Direction) :
  {target < states /\ Inside width h dir} + {~ (target < states /\ Inside width h dir)}.
Proof.
  destruct (lt_dec target states), (inside_dec width h dir);
    [left; auto|right; intuition|right; intuition|right; intuition].
Defined.

Theorem moveHead_flatten : forall c q w dir, Inside (span c) (length (tapeLeft c)) dir ->
  flatten (moveHead c q w dir) = setCell (flatten c) (length (tapeLeft c)) w /\
    length (tapeLeft (moveHead c q w dir)) = nextHead (length (tapeLeft c)) dir.
Proof.
  intros [state l a r] q w dir hi.
  assert (hs : setCell (flatten {| state := state; tapeLeft := l; tapeHead := a; tapeRight := r |})
      (length l) w = rev l ++ w :: r).
  { unfold flatten. simpl. replace (length l) with (length (rev l)) by apply length_rev.
    apply setCell_at_append. }
  simpl tapeLeft. rewrite hs. destruct dir; destruct l; destruct r;
    unfold Inside, span in hi; simpl in hi; try lia;
    unfold moveHead, nextHead; simpl; split; try lia;
    unfold flatten; simpl; repeat rewrite <- app_assoc; reflexivity.
Qed.
Theorem inside_of_moveHead_span : forall c q w dir,
  span (moveHead c q w dir) = span c -> Inside (span c) (length (tapeLeft c)) dir.
Proof.
  intros [state l a r] q w dir hs. destruct dir; destruct l; destruct r;
    unfold moveHead in hs; unfold Inside; simpl in *; unfold span in *; simpl in *; lia.
Qed.
Theorem moveHead_cells : forall c q w dir, Inside (span c) (length (tapeLeft c)) dir ->
  forall i, i < span c ->
    cell (moveHead c q w dir) i = if Nat.eq_dec i (length (tapeLeft c)) then w else cell c i.
Proof.
  intros c q w dir hi i hb. unfold cell.
  rewrite (proj1 (moveHead_flatten c q w dir hi)). apply setCell_nth;
    rewrite flatten_length; unfold span in *; lia.
Qed.
Theorem config_eq_of_cells : forall c d, state c = state d ->
  length (tapeLeft c) = length (tapeLeft d) -> span c = span d ->
  (forall i, i < span c -> cell c i = cell d i) -> c = d.
Proof.
  intros c d hq hh hw hc. apply flatten_injective; auto.
  apply nth_ext with (d := blank) (d' := blank).
  - rewrite !flatten_length. exact hw.
  - intros i hi. apply hc. rewrite flatten_length in hi. exact hi.
Qed.
Theorem moveHead_matches : forall c d states width q w dir,
  span c = width -> span d = width -> state d < states ->
  (moveHead c q w dir = d <->
    q < states /\ Inside width (length (tapeLeft c)) dir /\ state d = q /\
      length (tapeLeft d) = nextHead (length (tapeLeft c)) dir /\
      forall i, i < width -> cell d i =
        if Nat.eq_dec i (length (tapeLeft c)) then w else cell c i).
Proof.
  intros c d states width q w dir hc hd hq.
  assert (hs : state (moveHead c q w dir) = q).
  { destruct c as [state l a r]. destruct dir; destruct l; destruct r; reflexivity. }
  split.
  - intro he. assert (hi : Inside (span c) (length (tapeLeft c)) dir).
    { apply inside_of_moveHead_span with q w. rewrite he, hc, hd. reflexivity. }
    split; [rewrite <- he, hs in hq; exact hq|]. split; [rewrite <- hc; exact hi|].
    split; [rewrite <- he, hs; reflexivity|]. split.
    + rewrite <- he. apply (proj2 (moveHead_flatten c q w dir hi)).
    + intros i hb. rewrite <- he. apply moveHead_cells; auto; lia.
  - intros [_ [hi [hstate [hhead hcells]]]].
    assert (hi' : Inside (span c) (length (tapeLeft c)) dir) by (rewrite hc; exact hi).
    assert (hwidth : span (moveHead c q w dir) = width).
    { rewrite <- flatten_length, (proj1 (moveHead_flatten c q w dir hi')),
        setCell_length, flatten_length. exact hc. }
    apply config_eq_of_cells.
    + rewrite hs. symmetry. exact hstate.
    + rewrite (proj2 (moveHead_flatten c q w dir hi')). symmetry. exact hhead.
    + lia.
    + intros i hb. rewrite moveHead_cells by (auto; lia). rewrite hcells by lia. reflexivity.
Qed.

Definition stateVar (base q : nat) : nat := base + q.
Definition headVar (base states h : nat) : nat := base + states + h.
Definition tapeBase (base states width i : nat) : nat := base + states + width + 4 * i.
Definition tapeVar (base states width i s : nat) : nat := tapeBase base states width i + s.
Definition RowRepresents (a : Assignment) (base states width : nat) (c : Config) : Prop :=
  span c = width /\ Selected a base states (state c) /\
    Selected a (base + states) width (length (tapeLeft c)) /\
    forall i, i < width -> Selected a (tapeBase base states width i) 4 (symbolIndex (cell c i)).
Definition rowCNF (base states width : nat) : CNF :=
  (oneHot base states ++ oneHot (base + states) width) ++
    flat_map (fun i => oneHot (tapeBase base states width i) 4) (seq 0 width).
Definition rowAssignment (base states width : nat) (c : Config) : Assignment := fun v =>
  if v <? base then false else if v <? base + states then v =? stateVar base (state c)
  else if v <? base + states + width then v =? headVar base states (length (tapeLeft c))
  else if v <? base + states + 5 * width then
    let k := v - (base + states + width) in k mod 4 =? symbolIndex (cell c (k / 4))
  else false.

Lemma eqb_add_left : forall k i j, (k + i =? k + j) = (i =? j).
Proof. induction k; intros; simpl; auto. Qed.

Theorem rowAssignment_state : forall base states width c q, q < states ->
  rowAssignment base states width c (base + q) = (q =? state c).
Proof.
  intros base states width c q hq.
  assert (h0 : (base + q <? base) = false) by (apply Nat.ltb_ge; lia).
  assert (h1 : (base + q <? base + states) = true) by (apply Nat.ltb_lt; lia).
  unfold rowAssignment, stateVar. rewrite h0, h1. apply eqb_add_left.
Qed.
Theorem rowAssignment_head : forall base states width c h, h < width ->
  rowAssignment base states width c (base + states + h) = (h =? length (tapeLeft c)).
Proof.
  intros base states width c h hh.
  assert (h0 : (base + states + h <? base) = false) by (apply Nat.ltb_ge; lia).
  assert (h1 : (base + states + h <? base + states) = false) by (apply Nat.ltb_ge; lia).
  assert (h2 : (base + states + h <? base + states + width) = true) by (apply Nat.ltb_lt; lia).
  unfold rowAssignment, headVar. rewrite h0, h1, h2. apply eqb_add_left.
Qed.
Theorem rowAssignment_cell : forall base states width c i s, i < width -> s < 4 ->
  rowAssignment base states width c (tapeVar base states width i s) = (s =? symbolIndex (cell c i)).
Proof.
  intros base states width c i s hi hs.
  assert (h0 : (tapeVar base states width i s <? base) = false) by
    (apply Nat.ltb_ge; unfold tapeVar, tapeBase; lia).
  assert (h1 : (tapeVar base states width i s <? base + states) = false) by
    (apply Nat.ltb_ge; unfold tapeVar, tapeBase; lia).
  assert (h2 : (tapeVar base states width i s <? base + states + width) = false) by
    (apply Nat.ltb_ge; unfold tapeVar, tapeBase; lia).
  assert (h3 : (tapeVar base states width i s <? base + states + 5 * width) = true) by
    (apply Nat.ltb_lt; unfold tapeVar, tapeBase; lia).
  assert (hk : tapeVar base states width i s - (base + states + width) = 4 * i + s)
    by (unfold tapeVar, tapeBase; lia).
  assert (hd : (4 * i + s) / 4 = i).
  { replace (4 * i + s) with (i * 4 + s) by lia.
    rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia. }
  assert (hm : (4 * i + s) mod 4 = s).
  { replace (4 * i + s) with (s + i * 4) by lia.
    rewrite Nat.Div0.mod_add by lia. apply Nat.mod_small. lia. }
  unfold rowAssignment. rewrite h0, h1, h2, h3, hk, hd, hm. reflexivity.
Qed.

Theorem rowAssignment_represents : forall base states width c,
  span c = width -> state c < states ->
    RowRepresents (rowAssignment base states width c) base states width c.
Proof.
  intros base states width c hc hq.
  assert (hh : length (tapeLeft c) < width) by (unfold span in hc; lia).
  unfold RowRepresents. split; [exact hc|]. split.
  - unfold Selected. split; [exact hq|]. split.
    + rewrite rowAssignment_state by exact hq. apply Nat.eqb_refl.
    + intros q hb he. rewrite rowAssignment_state in he by exact hb. apply Nat.eqb_eq. exact he.
  - split.
    + unfold Selected. split; [exact hh|]. split.
      * rewrite rowAssignment_head by exact hh. apply Nat.eqb_refl.
      * intros h hb he. rewrite rowAssignment_head in he by exact hb. apply Nat.eqb_eq. exact he.
    + intros i hi. unfold Selected. split; [apply symbolIndex_lt|]. split.
      * change (rowAssignment base states width c (tapeVar base states width i (symbolIndex (cell c i))) = true).
        rewrite rowAssignment_cell by (auto; apply symbolIndex_lt). apply Nat.eqb_refl.
      * intros s hs he. change (rowAssignment base states width c (tapeVar base states width i s) = true) in he.
        rewrite rowAssignment_cell in he by assumption. apply Nat.eqb_eq. exact he.
Qed.

Theorem rowRepresents_models : forall a base states width c,
  RowRepresents a base states width c -> evalCNF a (rowCNF base states width) = true.
Proof.
  intros a base states width c [_ [hq [hh ht]]]. unfold rowCNF.
  rewrite !evalCNF_append, !andb_true_iff, !oneHot_selected, evalCNF_flatMap.
  split; [split; [exists (state c); exact hq|exists (length (tapeLeft c)); exact hh]|].
  intros i hi. apply in_seq in hi. apply oneHot_selected. exists (symbolIndex (cell c i)). apply ht. lia.
Qed.

Definition selectedIndex (a : Assignment) (base size : nat) : nat :=
  match find (fun i => a (base + i)) (seq 0 size) with Some v => v | None => 0 end.

Lemma find_selected : forall a base v xs, In v xs -> a (base + v) = true ->
  (forall j, In j xs -> a (base + j) = true -> j = v) ->
  find (fun i => a (base + i)) xs = Some v.
Proof.
  intros a base v xs. induction xs as [|j xs ih]; intros hv ht hu; [contradiction|].
  simpl. destruct (a (base + j)) eqn:hj.
  - f_equal. apply hu; [left; reflexivity|exact hj].
  - apply ih; auto.
    + destruct hv as [he|he]; [subst; congruence|exact he].
    + intros k hk. apply hu. right. exact hk.
Qed.

Theorem selectedIndex_selected : forall a base size v,
  Selected a base size v -> selectedIndex a base size = v.
Proof.
  intros a base size v [hv [ht hu]]. unfold selectedIndex.
  rewrite (find_selected a base v (seq 0 size)); auto.
  - apply in_seq. lia.
  - intros j hj. apply hu. apply in_seq in hj. lia.
Qed.

Lemma split_at_head : forall h xs, h < length xs ->
  firstn h xs ++ nth h xs blank :: skipn (h + 1) xs = xs.
Proof.
  induction h as [|h ih]; intros [|x xs] hh; simpl in *; try lia.
  - reflexivity.
  - f_equal. apply ih. lia.
Qed.

Theorem decodeConfig_shape : forall q h xs, h < length xs ->
  flatten (decodeConfig q h xs) = xs /\
    length (tapeLeft (decodeConfig q h xs)) = h /\ span (decodeConfig q h xs) = length xs.
Proof.
  intros q h xs hh.
  assert (hf : flatten (decodeConfig q h xs) = xs).
  { unfold flatten, decodeConfig. simpl. rewrite rev_involutive. apply split_at_head. exact hh. }
  split; [exact hf|]. split.
  - unfold decodeConfig. simpl. rewrite length_rev, length_firstn, Nat.min_l by lia. reflexivity.
  - rewrite <- flatten_length, hf. reflexivity.
Qed.

Definition decodeRow (a : Assignment) (base states width : nat) : Config :=
  decodeConfig (selectedIndex a base states) (selectedIndex a (base + states) width)
    (map (fun i => symbolOfIndex (selectedIndex a (tapeBase base states width i) 4)) (seq 0 width)).

(** Every satisfying row extracts a configuration by bounded, constructive search. *)
Theorem rowCNF_models : forall a base states width,
  evalCNF a (rowCNF base states width) = true <->
    RowRepresents a base states width (decodeRow a base states width).
Proof.
  intros a base states width. split.
  - intro hf. unfold rowCNF in hf.
    rewrite !evalCNF_append, !andb_true_iff, !oneHot_selected, evalCNF_flatMap in hf.
    destruct hf as [[[q hq] [h hh]] ht].
    assert (hshape := decodeConfig_shape q h
      (map (fun i => symbolOfIndex (selectedIndex a (tapeBase base states width i) 4)) (seq 0 width))).
    assert (hb : h < length (map (fun i => symbolOfIndex
      (selectedIndex a (tapeBase base states width i) 4)) (seq 0 width))).
    { rewrite length_map, length_seq. exact (proj1 hh). }
    specialize (hshape hb). destruct hshape as [hflat [hhead hspan]].
    unfold decodeRow, RowRepresents.
    rewrite (selectedIndex_selected _ _ _ _ hq), (selectedIndex_selected _ _ _ _ hh).
    split; [rewrite hspan, length_map, length_seq; reflexivity|]. split; [exact hq|].
    split; [rewrite hhead; exact hh|]. intros i hi.
    assert (hin : In i (seq 0 width)) by (apply in_seq; lia).
    pose proof (ht i hin) as hs. apply oneHot_selected in hs. destruct hs as [s hs].
    unfold cell. rewrite hflat.
    rewrite nth_indep with (d' := symbolOfIndex (selectedIndex a (tapeBase base states width 0) 4))
      by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (fun j => symbolOfIndex (selectedIndex a (tapeBase base states width j) 4))
      (seq 0 width) 0 i), seq_nth by lia.
    simpl. rewrite (selectedIndex_selected _ _ _ _ hs), symbolIndex_of_lt by exact (proj1 hs).
    exact hs.
  - apply rowRepresents_models.
Qed.

Theorem decodeRow_represents : forall a base states width c,
  RowRepresents a base states width c -> decodeRow a base states width = c.
Proof.
  intros a base states width c hc.
  assert (hd : RowRepresents a base states width (decodeRow a base states width)).
  { apply rowCNF_models. apply rowRepresents_models with c. exact hc. }
  destruct hc as [hc [hq [hh ht]]]. destruct hd as [hd [dq [dh dt]]].
  apply config_eq_of_cells.
  - apply (proj2 (proj2 hq)); [exact (proj1 dq)|exact (proj1 (proj2 dq))].
  - apply (proj2 (proj2 hh)); [exact (proj1 dh)|exact (proj1 (proj2 dh))].
  - lia.
  - intros i hi. apply symbol_index_injective. apply (proj2 (proj2 (ht i ltac:(lia))));
      [apply symbolIndex_lt|apply (proj1 (proj2 (dt i ltac:(lia))))].
Qed.

Theorem selected_true_iff : forall a base size v j,
  Selected a base size v -> j < size -> (a (base + j) = true <-> j = v).
Proof. intros a base size v j [_ [hv hu]] hj. split; [apply hu; exact hj|intro he; subst; exact hv]. Qed.

Definition guard (base states width q h s : nat) : Clause :=
  [mkLit (stateVar base q) true; mkLit (headVar base states h) true;
    mkLit (tapeVar base states width h s) true].
Lemma positive_lit : forall a v, evalLit a (mkLit v true) = true <-> a v = true.
Proof. intros. unfold evalLit. simpl. rewrite Bool.eqb_true_iff. reflexivity. Qed.
Lemma positive_clause : forall a v, evalClause a [mkLit v true] = true <-> a v = true.
Proof. intros. cbn [evalClause]. rewrite orb_false_r. apply positive_lit. Qed.
Theorem guard_models : forall a base states width c,
  RowRepresents a base states width c -> forall q h s, q < states -> h < width -> s < 4 ->
  ((forall l, In l (guard base states width q h s) -> evalLit a l = true) <->
    q = state c /\ h = length (tapeLeft c) /\ symbolOfIndex s = tapeHead c).
Proof.
  intros a base states width c [_ [hcq [hch hct]]] q h s hq hh hs.
  assert (hg : (forall l, In l (guard base states width q h s) -> evalLit a l = true) <->
      a (base + q) = true /\ a (base + states + h) = true /\ a (tapeBase base states width h + s) = true).
  { unfold guard, stateVar, headVar, tapeVar. split.
    - intro hf. split; [apply positive_lit; apply hf; simpl; auto|]. split;
        apply positive_lit; apply hf; simpl; auto.
    - intros [hf [hh' ht]] l [he|[he|[he|[]]]]; subst l; apply positive_lit; assumption. }
  rewrite hg, (selected_true_iff _ _ _ _ _ hcq hq),
    (selected_true_iff _ _ _ _ _ hch hh), (selected_true_iff _ _ _ _ _ (hct h hh) hs).
  split; intros [hq' [hh' he]]; repeat split; auto.
  - rewrite he, hh', cell_head, symbolOfIndex_index. reflexivity.
  - rewrite hh', cell_head, <- he, symbolIndex_of_lt by exact hs. reflexivity.
Qed.

Definition copyRules (prem : Clause) (base next states width h : nat) (write : Symbol) : CNF :=
  flat_map (fun i => map (fun s =>
    implies (prem ++ [mkLit (tapeVar base states width i s) true])
      [mkLit (tapeVar next states width i (if Nat.eq_dec i h then symbolIndex write else s)) true])
    (seq 0 4)) (seq 0 width).
Definition instructionRules (m : Machine) (base next width q h s : nat) : CNF :=
  let states := length (program m) in let prem := guard base states width q h s in
  match instruction m q (symbolOfIndex s) with
  | halt _ => [implies prem []]
  | move target write dir => if moveAllowed_dec states width target h dir then
      [implies prem [mkLit (stateVar next target) true];
       implies prem [mkLit (headVar next states (nextHead h dir)) true]] ++
        copyRules prem base next states width h write
    else [implies prem []]
  end.
Definition transitionCNF (m : Machine) (base next width : nat) : CNF :=
  flat_map (fun q => flat_map (fun h => flat_map (fun s =>
    instructionRules m base next width q h s) (seq 0 4)) (seq 0 width)) (seq 0 (length (program m))).
Definition successorCNF (m : Machine) (base next width : nat) : CNF :=
  (rowCNF base (length (program m)) width ++ rowCNF next (length (program m)) width) ++
    transitionCNF m base next width.

Theorem copyRules_models : forall a prem base next states width h write,
  evalCNF a (copyRules prem base next states width h write) = true <->
    ((forall l, In l prem -> evalLit a l = true) ->
      forall i, i < width -> forall s, s < 4 -> a (tapeVar base states width i s) = true ->
        a (tapeVar next states width i (if Nat.eq_dec i h then symbolIndex write else s)) = true).
Proof.
  intros a prem base next states width h write. unfold copyRules.
  rewrite evalCNF_flatMap. split.
  - intros hf hp i hi s hs ht.
    specialize (hf i ltac:(apply in_seq; lia)). rewrite evalCNF_map in hf.
    specialize (hf s ltac:(apply in_seq; lia)). rewrite implies_models in hf.
    apply positive_clause. apply hf. intros l hl. apply in_app_or in hl.
    destruct hl as [hl|[he|[]]]; [apply hp; exact hl|subst; apply positive_lit; exact ht].
  - intros hf i hi. apply in_seq in hi. rewrite evalCNF_map.
    intros s hs. apply in_seq in hs. rewrite implies_models, positive_clause. intro hp.
    apply hf; try lia.
    + intros l hl. apply hp. apply in_or_app. left. exact hl.
    + apply positive_lit. apply hp. apply in_or_app. right. simpl. auto.
Qed.

Theorem copyRules_cells : forall a base next states width h write c d,
  RowRepresents a base states width c -> RowRepresents a next states width d ->
  ((forall i, i < width -> forall s, s < 4 -> a (tapeVar base states width i s) = true ->
      a (tapeVar next states width i (if Nat.eq_dec i h then symbolIndex write else s)) = true) <->
    forall i, i < width -> cell d i = if Nat.eq_dec i h then write else cell c i).
Proof.
  intros a base next states width h write c d [_ [_ [_ hc]]] [_ [_ [_ hd]]]. split.
  - intros hf i hi. destruct (hc i hi) as [_ [ht _]].
    pose proof (hf i hi _ (symbolIndex_lt (cell c i)) ht) as ho.
    destruct (hd i hi) as [_ [_ hu]].
    assert (hb : (if Nat.eq_dec i h then symbolIndex write else symbolIndex (cell c i)) < 4).
    { destruct (Nat.eq_dec i h); apply symbolIndex_lt. }
    specialize (hu _ hb ho). apply symbol_index_injective.
    destruct (Nat.eq_dec i h); symmetry; exact hu.
  - intros hf i hi s hs ht. destruct (hc i hi) as [_ [_ hu]].
    specialize (hu s hs ht). destruct (hd i hi) as [_ [ho _]].
    assert (he : (if Nat.eq_dec i h then symbolIndex write else s) = symbolIndex (cell d i)).
    { rewrite (hf i hi), hu. destruct (Nat.eq_dec i h); reflexivity. }
    unfold tapeVar. rewrite he. exact ho.
Qed.

Theorem instructionRules_models : forall m base next width q h s a,
  evalCNF a (instructionRules m base next width q h s) = true <->
    ((forall l, In l (guard base (length (program m)) width q h s) -> evalLit a l = true) ->
      match instruction m q (symbolOfIndex s) with
      | halt _ => False
      | move target write dir => target < length (program m) /\ Inside width h dir /\
          a (stateVar next target) = true /\ a (headVar next (length (program m)) (nextHead h dir)) = true /\
          forall i, i < width -> forall t, t < 4 -> a (tapeVar base (length (program m)) width i t) = true ->
            a (tapeVar next (length (program m)) width i
              (if Nat.eq_dec i h then symbolIndex write else t)) = true
      end).
Proof.
  intros m base next width q h s a. unfold instructionRules.
  destruct (instruction m q (symbolOfIndex s)) as [b|target write dir].
  - cbn [evalCNF]. rewrite andb_true_r, implies_models. simpl evalClause. split.
    + intros hf hp. specialize (hf hp). discriminate.
    + intros hf hp. contradiction (hf hp).
  - destruct (moveAllowed_dec (length (program m)) width target h dir) as [hi|hi].
    + rewrite evalCNF_append, andb_true_iff, copyRules_models.
      cbn [evalCNF]. rewrite andb_true_r, andb_true_iff, !implies_models, !positive_clause.
      split.
      * intros [[hq hh] ht] hp. destruct hi as [htarget hinside]. repeat split; auto.
      * intro hf. split.
        -- split; intro hp; [exact (proj1 (proj2 (proj2 (hf hp))))|
             exact (proj1 (proj2 (proj2 (proj2 (hf hp)))))] .
        -- intro hp. exact (proj2 (proj2 (proj2 (proj2 (hf hp))))).
    + cbn [evalCNF]. rewrite andb_true_r, implies_models. simpl evalClause. split.
      * intros hf hp. specialize (hf hp). discriminate.
      * intros hf hp. exfalso. apply hi. destruct (hf hp) as [ht [hin _]]. auto.
Qed.

Theorem nextHead_lt : forall width h dir, h < width -> Inside width h dir -> nextHead h dir < width.
Proof. intros width h [] hh hi; unfold nextHead, Inside in *; lia. Qed.

Theorem instructionRules_step : forall m base next width q h s a c d,
  RowRepresents a base (length (program m)) width c ->
  RowRepresents a next (length (program m)) width d ->
  q < length (program m) -> h < width -> s < 4 ->
  (evalCNF a (instructionRules m base next width q h s) = true <->
    ((forall l, In l (guard base (length (program m)) width q h s) -> evalLit a l = true) -> step m c = inr d)).
Proof.
  intros m base next width q h s a c d hc hd hq hh hs.
  rewrite instructionRules_models. split.
  - intros hf hp. pose proof (hf hp) as ho.
    destruct (proj1 (guard_models a _ _ _ c hc q h s hq hh hs) hp) as [heq [heh hes]].
    subst q h. rewrite hes in ho. unfold step.
    destruct (instruction m (state c) (tapeHead c)) as [b|target write dir] eqn:hin;
      [contradiction|].
    destruct ho as [ht [hi [hstate [hhead hcopy]]]].
    destruct hc as [hcw [hcq [hch hct]]]. destruct hd as [hdw [hdq [hdh hdt]]].
    assert (heq : target = state d) by (apply (proj2 (proj2 hdq)); exact ht || exact hstate).
    assert (heh : nextHead (length (tapeLeft c)) dir = length (tapeLeft d)).
    { apply (proj2 (proj2 hdh)); [apply nextHead_lt; assumption|exact hhead]. }
    assert (hrows : RowRepresents a base (length (program m)) width c /\
      RowRepresents a next (length (program m)) width d) by (unfold RowRepresents; auto).
    pose proof (proj1 (copyRules_cells a base next _ width _ write c d (proj1 hrows) (proj2 hrows)) hcopy) as hcells.
    f_equal. apply (proj2 (moveHead_matches c d _ width target write dir hcw hdw (proj1 hdq))).
    repeat split; auto.
  - intros hf hp. pose proof (hf hp) as hstep.
    destruct (proj1 (guard_models a _ _ _ c hc q h s hq hh hs) hp) as [heq [heh hes]].
    subst q h. rewrite hes. unfold step in hstep.
    destruct (instruction m (state c) (tapeHead c)) as [b|target write dir] eqn:hin;
      [discriminate|]. inversion hstep as [hmove].
    destruct hd as [hdw [hdq [hdh hdt]]].
    destruct (proj1 (moveHead_matches c d _ width target write dir (proj1 hc) hdw (proj1 hdq)) hmove)
      as [ht [hi [hstate [hhead hcells]]]].
    split; [exact ht|]. split; [exact hi|]. split.
    + unfold stateVar. rewrite <- hstate. exact (proj1 (proj2 hdq)).
    + split.
      * unfold headVar. rewrite <- hhead. exact (proj1 (proj2 hdh)).
      * apply (proj2 (copyRules_cells a base next _ width _ write c d hc
          ltac:(unfold RowRepresents; auto))). exact hcells.
Qed.

Theorem transitionCNF_step : forall m base next width a c d,
  RowRepresents a base (length (program m)) width c ->
  RowRepresents a next (length (program m)) width d ->
  (evalCNF a (transitionCNF m base next width) = true <-> step m c = inr d).
Proof.
  intros m base next width a c d hc hd. unfold transitionCNF. rewrite evalCNF_flatMap. split.
  - intro hf. pose proof (proj1 (proj1 (proj2 hc))) as hq.
    pose proof (proj1 (proj1 (proj2 (proj2 hc)))) as hh.
    specialize (hf (state c) ltac:(apply in_seq; lia)). rewrite evalCNF_flatMap in hf.
    specialize (hf (length (tapeLeft c)) ltac:(apply in_seq; lia)). rewrite evalCNF_flatMap in hf.
    specialize (hf (symbolIndex (tapeHead c)) ltac:(apply in_seq; pose proof (symbolIndex_lt (tapeHead c)); lia)).
    apply (proj1 (instructionRules_step m base next width _ _ _ a c d hc hd hq hh
      (symbolIndex_lt (tapeHead c)))) in hf.
    apply hf. apply (proj2 (guard_models a _ _ _ c hc _ _ _ hq hh (symbolIndex_lt (tapeHead c)))).
    repeat split; auto. apply symbolOfIndex_index.
  - intros hstep q hq. apply in_seq in hq. rewrite evalCNF_flatMap.
    intros h hh. apply in_seq in hh. rewrite evalCNF_flatMap.
    intros s hs. apply in_seq in hs.
    apply (proj2 (instructionRules_step m base next width q h s a c d hc hd ltac:(lia) ltac:(lia) ltac:(lia))).
    intros _. exact hstep.
Qed.
Theorem successorCNF_step : forall m base next width a c d,
  RowRepresents a base (length (program m)) width c ->
  RowRepresents a next (length (program m)) width d ->
  (evalCNF a (successorCNF m base next width) = true <-> step m c = inr d).
Proof.
  intros m base next width a c d hc hd. unfold successorCNF.
  rewrite !evalCNF_append, (rowRepresents_models _ _ _ _ c hc),
    (rowRepresents_models _ _ _ _ d hd). simpl. apply transitionCNF_step; assumption.
Qed.
Theorem successorCNF_models : forall m base next width a,
  evalCNF a (successorCNF m base next width) = true <->
    RowRepresents a base (length (program m)) width (decodeRow a base (length (program m)) width) /\
    RowRepresents a next (length (program m)) width (decodeRow a next (length (program m)) width) /\
    step m (decodeRow a base (length (program m)) width) =
      inr (decodeRow a next (length (program m)) width).
Proof.
  intros m base next width a. split.
  - intro hf. pose proof hf as h. unfold successorCNF in h.
    rewrite !evalCNF_append, !andb_true_iff in h. destruct h as [[hc hd] ht].
    apply rowCNF_models in hc. apply rowCNF_models in hd.
    split; [exact hc|]. split; [exact hd|].
    apply (proj1 (successorCNF_step m base next width a _ _ hc hd)). exact hf.
  - intros [hc [hd hs]].
    apply (proj2 (successorCNF_step m base next width a _ _ hc hd)). exact hs.
Qed.
Theorem successorCNF_sound : forall m base next width a,
  evalCNF a (successorCNF m base next width) = true ->
    step m (decodeRow a base (length (program m)) width) =
      inr (decodeRow a next (length (program m)) width).
Proof. intros m base next width a hf. apply successorCNF_models in hf. exact (proj2 (proj2 hf)). Qed.
Theorem successorCNF_decoded_wrong_successor : forall m base next width a,
  step m (decodeRow a base (length (program m)) width) <>
    inr (decodeRow a next (length (program m)) width) ->
  evalCNF a (successorCNF m base next width) = false.
Proof.
  intros m base next width a hs. destruct (evalCNF a (successorCNF m base next width)) eqn:he;
    [|reflexivity]. exfalso. apply hs. apply successorCNF_sound. exact he.
Qed.
Theorem successorCNF_wrong_successor : forall m base next width a c d,
  RowRepresents a base (length (program m)) width c ->
  RowRepresents a next (length (program m)) width d -> step m c <> inr d ->
  evalCNF a (successorCNF m base next width) = false.
Proof.
  intros m base next width a c d hc hd hs.
  destruct (evalCNF a (successorCNF m base next width)) eqn:he; [|reflexivity].
  exfalso. apply hs. apply (proj1 (successorCNF_step m base next width a c d hc hd)). exact he.
Qed.

Lemma flatMap_length_le : forall (A B : Type) (xs : list A) (f : A -> list B) bound,
  (forall x, In x xs -> length (f x) <= bound) -> length (flat_map f xs) <= length xs * bound.
Proof.
  intros A B xs f bound. induction xs as [|x xs IH]; intro h; simpl; [lia|].
  rewrite length_app. specialize (IH ltac:(intros; apply h; right; assumption)).
  pose proof (h x (or_introl eq_refl)). nia.
Qed.

Theorem rowCNF_length : forall base states width,
  length (rowCNF base states width) <= states * states + width * width + 17 * width + 2.
Proof.
  intros base states width. pose proof (oneHot_length base states) as hs.
  pose proof (oneHot_length (base + states) width) as hh.
  assert (ht : length (flat_map (fun i => oneHot (tapeBase base states width i) 4) (seq 0 width)) <= width * 17).
  { rewrite <- (length_seq width 0) at 2. apply flatMap_length_le.
    intros i _. apply oneHot_length. }
  unfold rowCNF. rewrite !length_app. lia.
Qed.

Theorem rowCNF_bounds : forall base states width,
  VarsBelow (base + states + 5 * width) (rowCNF base states width) /\
    forall c, In c (rowCNF base states width) -> length c <= states + width + 6.
Proof.
  intros base states width.
  destruct (oneHot_bounds base states) as [hsv hsw].
  destruct (oneHot_bounds (base + states) width) as [hhv hhw].
  split.
  - intros c hc l hl. unfold rowCNF in hc. apply in_app_or in hc.
    destruct hc as [hc|hc].
    + apply in_app_or in hc. destruct hc as [hc|hc];
        [specialize (hsv c hc l hl)|specialize (hhv c hc l hl)]; lia.
    + apply in_flat_map in hc. destruct hc as [i [hi hc]]. apply in_seq in hi.
      pose proof (proj1 (oneHot_bounds (tapeBase base states width i) 4) c hc l hl) as h.
      unfold tapeBase in h. lia.
  - intros c hc. unfold rowCNF in hc. apply in_app_or in hc. destruct hc as [hc|hc].
    + apply in_app_or in hc. destruct hc as [hc|hc];
        [specialize (hsw c hc)|specialize (hhw c hc)]; lia.
    + apply in_flat_map in hc. destruct hc as [i [hi hc]].
      pose proof (proj2 (oneHot_bounds (tapeBase base states width i) 4) c hc) as h. lia.
Qed.

Lemma copyRules_length : forall prem base next states width h write,
  length (copyRules prem base next states width h write) <= 4 * width.
Proof.
  intros. unfold copyRules. replace (4 * width) with (length (seq 0 width) * 4)
    by (rewrite length_seq; lia). apply flatMap_length_le.
  intros i _. rewrite length_map, length_seq. lia.
Qed.
Theorem instructionRules_length : forall m base next width q h s,
  length (instructionRules m base next width q h s) <= 4 * width + 2.
Proof.
  intros. unfold instructionRules. destruct (instruction m q (symbolOfIndex s)) as [b|target write dir];
    [simpl; lia|]. destruct (moveAllowed_dec (length (program m)) width target h dir);
    [rewrite length_app; simpl length; pose proof (copyRules_length (guard base (length (program m)) width q h s)
       base next (length (program m)) width h write); lia|simpl; lia].
Qed.

Lemma implies_bounds : forall bound prem conclusion,
  (forall l, In l prem -> var l < bound) ->
  (forall l, In l conclusion -> var l < bound) ->
  forall l, In l (implies prem conclusion) -> var l < bound.
Proof.
  intros bound prem conclusion hp ht l hl. unfold implies in hl. apply in_app_or in hl.
  destruct hl as [hl|hl]; [apply in_map_iff in hl; destruct hl as [v [he hv]]; subst;
    unfold negate; simpl; apply hp; exact hv|apply ht; exact hl].
Qed.

Theorem instructionRules_bounds : forall m base next width q h s,
  q < length (program m) -> h < width -> s < 4 ->
  VarsBelow (Nat.max base next + length (program m) + 5 * width)
    (instructionRules m base next width q h s) /\
    forall c, In c (instructionRules m base next width q h s) -> length c <= 5.
Proof.
  intros m base next width q h s hq hh hs.
  set (bound := Nat.max base next + length (program m) + 5 * width).
  pose proof (Nat.le_max_l base next) as hb. pose proof (Nat.le_max_r base next) as hn.
  assert (hg : forall l, In l (guard base (length (program m)) width q h s) -> var l < bound).
  { intros l hl. unfold guard in hl. simpl in hl. destruct hl as [he|[he|[he|[]]]];
      subst l; cbn [var]; unfold stateVar, headVar, tapeVar, tapeBase, bound; lia. }
  assert (hforbid : (forall l, In l (implies (guard base (length (program m)) width q h s) []) -> var l < bound) /\
    length (implies (guard base (length (program m)) width q h s) []) <= 5).
  { split; [apply implies_bounds; [exact hg|simpl; tauto]|unfold implies, guard; simpl; lia]. }
  unfold instructionRules.
  destruct (instruction m q (symbolOfIndex s)) as [b|target write dir].
  - split; intros c hc; simpl in hc; destruct hc as [he|[]]; subst c;
      [exact (proj1 hforbid)|exact (proj2 hforbid)].
  - destruct (moveAllowed_dec (length (program m)) width target h dir) as [[ht hi]|hi].
    + pose proof (nextHead_lt width h dir hh hi) as hh'.
      assert (hvq : stateVar next target < bound) by (unfold stateVar, bound; lia).
      assert (hvh : headVar next (length (program m)) (nextHead h dir) < bound) by (unfold headVar, bound; lia).
      assert (hcopy : forall c, In c (copyRules (guard base (length (program m)) width q h s)
          base next (length (program m)) width h write) ->
          (forall l, In l c -> var l < bound) /\ length c <= 5).
      { intros c hc. unfold copyRules in hc. apply in_flat_map in hc.
        destruct hc as [i [hi' hc]]. apply in_seq in hi'. apply in_map_iff in hc.
        destruct hc as [t [he ht']]. apply in_seq in ht'. subst c. split.
        - apply implies_bounds.
          + intros l hl. apply in_app_or in hl. destruct hl as [hl|[he|[]]];
              [apply hg; exact hl|subst l; simpl; unfold tapeVar, tapeBase, bound; lia].
          + intros l [he|[]]. subst l. simpl. pose proof (symbolIndex_lt write) as hw.
            unfold tapeVar, tapeBase, bound. destruct (Nat.eq_dec i h); lia.
        - unfold implies, guard. rewrite length_app, length_map, length_app. simpl. lia. }
      split.
      * intros c hc l hl. apply in_app_or in hc. destruct hc as [[he|[he|[]]]|hc].
        -- subst c. apply implies_bounds with (guard base (length (program m)) width q h s)
             [mkLit (stateVar next target) true]; [exact hg|simpl; intros v [he|[]]; subst; exact hvq|exact hl].
        -- subst c. apply implies_bounds with (guard base (length (program m)) width q h s)
             [mkLit (headVar next (length (program m)) (nextHead h dir)) true];
             [exact hg|simpl; intros v [he|[]]; subst; exact hvh|exact hl].
        -- exact (proj1 (hcopy c hc) l hl).
      * intros c hc. apply in_app_or in hc. destruct hc as [[he|[he|[]]]|hc];
          [subst; unfold implies, guard; simpl; lia|subst; unfold implies, guard; simpl; lia|exact (proj2 (hcopy c hc))].
    + split; intros c hc; simpl in hc; destruct hc as [he|[]]; subst c;
        [exact (proj1 hforbid)|exact (proj2 hforbid)].
Qed.

Definition successorCount (m : Machine) (width : nat) : nat :=
  2 * (length (program m) * length (program m) + width * width + 17 * width + 2) +
    4 * length (program m) * width * (4 * width + 2).
Definition successorSize (m : Machine) (base next width : nat) : nat :=
  2 * successorCount m width *
    (1 + (length (program m) + width + 6) * (Nat.max base next + length (program m) + 5 * width + 1)).

Theorem successorCNF_length : forall m base next width,
  length (successorCNF m base next width) <= successorCount m width.
Proof.
  intros m base next width.
  assert (ht : length (transitionCNF m base next width) <= 4 * length (program m) * width * (4 * width + 2)).
  { unfold transitionCNF.
    replace (4 * length (program m) * width * (4 * width + 2)) with
      (length (seq 0 (length (program m))) * (width * (4 * (4 * width + 2)))) by (rewrite length_seq; nia).
    apply flatMap_length_le. intros q _.
    rewrite <- (length_seq width 0) at 2. apply flatMap_length_le. intros h _.
    replace (4 * (4 * width + 2)) with (length (seq 0 4) * (4 * width + 2)) by reflexivity.
    apply flatMap_length_le. intros s _. apply instructionRules_length. }
  pose proof (rowCNF_length base (length (program m)) width).
  pose proof (rowCNF_length next (length (program m)) width).
  unfold successorCNF, successorCount. rewrite !length_app. lia.
Qed.

Theorem successorCNF_bounds : forall m base next width,
  VarsBelow (Nat.max base next + length (program m) + 5 * width) (successorCNF m base next width) /\
    forall c, In c (successorCNF m base next width) -> length c <= length (program m) + width + 6.
Proof.
  intros m base next width.
  destruct (rowCNF_bounds base (length (program m)) width) as [hbv hbw].
  destruct (rowCNF_bounds next (length (program m)) width) as [hnv hnw].
  assert (ht : forall c, In c (transitionCNF m base next width) ->
    (forall l, In l c -> var l < Nat.max base next + length (program m) + 5 * width) /\ length c <= 5).
  { intros c hc. unfold transitionCNF in hc. apply in_flat_map in hc.
    destruct hc as [q [hq hc]]. apply in_seq in hq. apply in_flat_map in hc.
    destruct hc as [h [hh hc]]. apply in_seq in hh. apply in_flat_map in hc.
    destruct hc as [s [hs hc]]. apply in_seq in hs.
    destruct (instructionRules_bounds m base next width q h s ltac:(lia) ltac:(lia) ltac:(lia)) as [hv hw].
    split; [exact (hv c hc)|exact (hw c hc)]. }
  split.
  - intros c hc l hl. unfold successorCNF in hc. apply in_app_or in hc.
    destruct hc as [hc|hc]; [apply in_app_or in hc; destruct hc as [hc|hc]|exact (proj1 (ht c hc) l hl)].
    + specialize (hbv c hc l hl). pose proof (Nat.le_max_l base next). lia.
    + specialize (hnv c hc l hl). pose proof (Nat.le_max_r base next). lia.
  - intros c hc. unfold successorCNF in hc. apply in_app_or in hc. destruct hc as [hc|hc].
    + apply in_app_or in hc. destruct hc as [hc|hc]; [apply hbw|apply hnw]; exact hc.
    + pose proof (proj2 (ht c hc)). lia.
Qed.

Theorem successorCNF_encoded_size : forall m base next width,
  length (encodeCNF (successorCNF m base next width)) <= successorSize m base next width.
Proof.
  intros m base next width. destruct (successorCNF_bounds m base next width) as [hv hw].
  pose proof (cnf_encoded_size _ _ _ hv hw) as h.
  pose proof (successorCNF_length m base next width) as hc.
  unfold successorSize. eapply Nat.le_trans; [exact h|]. apply Nat.mul_le_mono_r. lia.
Qed.

End SuccessorCNF.
