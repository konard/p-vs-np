From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import CircuitModel.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue626.rocq Require Import NandCompiler Window Simulation.
Import ListNotations.

(** Rocq twin of Correctness.lean: row encoding and NAND simulation
    correctness, followed by the inclusion P in P/poly. *)
Module SimulationCorrectness.
Import Complexity NandCompiler Simulation.

Definition bit (s : Symbol) (lane : nat) : bool :=
  if lane =? 0 then 2 <=? symbolIndex s else symbolIndex s mod 2 =? 1.
Definition done (c : bool + Config) : bool := match c with inl _ => true | inr _ => false end.
Definition answer (c : bool + Config) : bool := match c with inl b => b | inr _ => false end.
Definition scanned (c : bool + Config) : Symbol := match c with inl _ => blank | inr c => tapeHead c end.
Definition stateBit (c : bool + Config) (q : nat) : bool :=
  match c with inl _ => false | inr c => state c =? q end.
Definition tape (c : bool + Config) (side : bool) (cell : nat) : Symbol :=
  match c with inl _ => blank | inr c => nth cell (if side then tapeRight c else tapeLeft c) blank end.

Record Encodes (m : Machine) (cells : nat) (x : list bool)
  (r : list Expr) (c : bool + Config) : Prop := {
  doneBit : eval x (ref r 0) = done c;
  answerBit : eval x (ref r 1) = answer c;
  headBits : forall lane, lane < 2 -> eval x (ref r (2 + lane)) = bit (scanned c) lane;
  stateBits : forall q, q < length (program m) -> eval x (ref r (4 + q)) = stateBit c q;
  tapeBits : forall side cell lane, cell < cells -> lane < 2 ->
    eval x (tapeRef (length (program m)) cells r side cell lane) = bit (tape c side cell) lane
}.
Arguments doneBit {m cells x r c} _.
Arguments answerBit {m cells x r c} _.
Arguments headBits {m cells x r c} _ _ _.
Arguments stateBits {m cells x r c} _ _ _.
Arguments tapeBits {m cells x r c} _ _ _ _ _ _.

Lemma eval_symbolBit : forall x s lane, eval x (symbolBit s lane) = bit s lane.
Proof. reflexivity. Qed.
Lemma eval_ref : forall x r i, eval x (ref r i) = nth i (map (eval x) r) false.
Proof.
  intros x r; induction r; intros []; unfold ref in *; simpl; auto.
Qed.
Lemma ref_range : forall x f k i, i < k ->
  eval x (ref (map f (seq 0 k)) i) = eval x (f i).
Proof.
  intros x f k i hi. unfold ref.
  rewrite nth_indep with (d' := f 0) by (rewrite length_map,length_seq; lia).
  rewrite map_nth, seq_nth by lia. replace (0 + i) with i by lia. reflexivity.
Qed.

Lemma chooseSymbol_eval : forall m cells x r c, Encodes m cells x r c ->
  forall f, eval x (chooseSymbol r f) = eval x (f (scanned c)).
Proof.
  intros m cells x r c h f.
  pose proof (headBits h 0 ltac:(lia)) as h0.
  pose proof (headBits h 1 ltac:(lia)) as h1.
  replace (2 + 0) with 2 in h0 by lia. replace (2 + 1) with 3 in h1 by lia.
  unfold chooseSymbol. rewrite !eval_mux,h0,h1.
  destruct c as [b|c]; [reflexivity|]. unfold scanned. destruct (tapeHead c); reflexivity.
Qed.

Lemma nth_nil : forall (A : Type) (i : nat) (d : A), nth i [] d = d.
Proof. intros A [] d; reflexivity. Qed.
Lemma nth_lookup : forall (A : Type) (l : list A) i d,
  (match nth_error l i with Some a => a | None => d end) = nth i l d.
Proof. intros A l; induction l; intros []; simpl; auto. Qed.

Lemma instruction_getD : forall m q s,
  instruction m q s = nth (symbolIndex s) (nth q (program m) []) (halt false).
Proof.
  intros m q s. unfold instruction. revert q.
  induction (program m) as [|row rows IH]; intros q; destruct q; simpl; auto.
  all: first [destruct s; reflexivity | apply nth_lookup].
Qed.

Lemma chooseState_eval : forall m cells x r c, Encodes m cells x r (inr c) ->
  forall f rows q, q + length rows <= length (program m) -> q <= state c ->
  eval x (chooseState m r f q rows) =
    eval x (f (nth (symbolIndex (tapeHead c)) (nth (state c - q) rows []) (halt false))).
Proof.
  intros m cells x r c h f rows. induction rows as [|row rows IH]; intros q hlen hq.
  - cbn [chooseState]. rewrite !nth_nil. reflexivity.
  - cbn [chooseState]. rewrite eval_mux.
    rewrite (stateBits h q ltac:(simpl in hlen; lia)). unfold stateBit.
    destruct (state c =? q) eqn:he.
    + apply Nat.eqb_eq in he. rewrite he, Nat.sub_diag. cbn [nth].
      apply chooseSymbol_eval with (m:=m) (cells:=cells) (c:=inr c). exact h.
    + apply Nat.eqb_neq in he.
      replace (state c - q) with (S (state c - (q + 1))) by lia. cbn [nth].
      apply IH; simpl in hlen; lia.
Qed.

Lemma chosen_instruction_eval : forall m cells x r c, Encodes m cells x r (inr c) ->
  forall f, eval x (chooseState m r f 0 (program m)) = eval x (f (instruction m (state c) (tapeHead c))).
Proof.
  intros. rewrite (chooseState_eval m cells x r c H f (program m) 0) by lia.
  rewrite Nat.sub_0_r, instruction_getD. reflexivity.
Qed.

Lemma pad_getD : forall k l i, i < k -> nth i (Window.pad k l) blank = nth i l blank.
Proof.
  induction k; intros l i hi; [lia|].
  destruct l; destruct i; simpl; auto; try (apply IHk; lia).
  pose proof (IHk [] i ltac:(lia)) as hp. rewrite nth_nil in hp. exact hp.
Qed.
Lemma tape_window : forall k c side i, i < k ->
  tape (inr (Window.window k c)) side i = tape (inr c) side i.
Proof. intros. destruct side; apply pad_getD; assumption. Qed.
Lemma moved_head : forall c q s d,
  tapeHead (moveHead c q s d) = match d with
  | stay => s | left => nth 0 (tapeLeft c) blank | right => nth 0 (tapeRight c) blank end.
Proof. intros [st l hd r] q s d. destruct d,l,r; reflexivity. Qed.
Lemma moved_state : forall c q s d, state (moveHead c q s d) = q.
Proof. intros [st l hd r] q s d. destruct d,l,r; reflexivity. Qed.
Lemma moved_tape : forall c q s d side cell,
  tape (inr (moveHead c q s d)) side cell = match d,side with
  | stay,_ => tape (inr c) side cell
  | left,false | right,true => tape (inr c) side (cell+1)
  | right,false | left,true => if cell =? 0 then s else tape (inr c) side (cell-1) end.
Proof.
  intros [st l hd r] q s d side cell. destruct d,side,l,r,cell; simpl;
    try rewrite Nat.sub_0_r; try rewrite Nat.add_1_r; reflexivity.
Qed.

Definition rowExpr m cells r i := mux (ref r 0)
  (if i =? 0 then lit true else if i =? 1 then ref r 1 else lit false)
  (chooseState m r (instructionBit m cells r i) 0 (program m)).
Lemma row_live : forall m cells x r c, Encodes m cells x r (inr c) -> forall i,
  eval x (rowExpr m cells r i) = eval x (instructionBit m cells r i (instruction m (state c) (tapeHead c))).
Proof.
  intros m cells x r c h i. unfold rowExpr. rewrite eval_mux,(doneBit h). cbn [done].
  apply chosen_instruction_eval with (cells:=cells). exact h.
Qed.
Lemma step_ref : forall m cells x r i, i < width (length (program m)) (cells-1) ->
  eval x (ref (stepExprs m cells r) i) = eval x (rowExpr m cells r i).
Proof. intros. apply ref_range. assumption. Qed.
Lemma rowIndex_lt : forall states cells (side : bool) cell lane, cell < cells -> lane < 2 ->
  4 + states + (if side then 2*cells else 0) + 2*cell + lane < width states cells.
Proof. intros. destruct side; unfold width; lia. Qed.

Lemma div2 : forall cell lane, lane < 2 -> (2*cell+lane)/2 = cell.
Proof.
  intros. replace (2*cell+lane) with (lane+cell*2) by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia. lia.
Qed.
Lemma mod2 : forall cell lane, lane < 2 -> (2*cell+lane) mod 2 = lane.
Proof.
  intros. replace (2*cell+lane) with (lane+cell*2) by lia.
  rewrite Nat.mod_add by lia. apply Nat.mod_small. lia.
Qed.

Lemma moved_tape_eval : forall m cells x r c, Encodes m cells x r (inr c) ->
  forall (side : bool) cell lane q s d, cell < cells-1 -> lane < 2 ->
  eval x (movedBit m cells r
    (4 + length (program m) + (if side then 2*(cells-1) else 0) + 2*cell+lane) q s d) =
  bit (tape (inr (moveHead c q s d)) side cell) lane.
Proof.
  intros m cells x r c h side cell lane q s d hc hl.
  set (i := 4 + length (program m) + (if side then 2*(cells-1) else 0) + 2*cell+lane).
  assert (h0 : (i =? 0) = false) by (apply Nat.eqb_neq; unfold i; destruct side; lia).
  assert (h1 : (i =? 1) = false) by (apply Nat.eqb_neq; unfold i; destruct side; lia).
  assert (h4 : (i <? 4) = false) by (apply Nat.ltb_ge; unfold i; destruct side; lia).
  assert (hq : (i <? 4 + length (program m)) = false)
    by (apply Nat.ltb_ge; unfold i; destruct side; lia).
  assert (hs : (2*(cells-1) <=? i-(4+length (program m))) = side).
  { destruct side; [apply Nat.leb_le|apply Nat.leb_gt]; unfold i; lia. }
  assert (ho : (if side then i-(4+length (program m))-2*(cells-1)
    else i-(4+length (program m))) = 2*cell+lane) by (destruct side; unfold i; lia).
  unfold movedBit. fold i. rewrite h0,h1,h4,hq. cbn zeta. rewrite hs,ho.
  rewrite div2,mod2 by assumption. rewrite moved_tape.
  destruct d,side; try (apply (tapeBits h); lia).
  all: destruct (cell =? 0); [apply eval_symbolBit|apply (tapeBits h); lia].
Qed.

Lemma row_halt : forall m cells x r b, Encodes m cells x r (inl b) -> forall i,
  eval x (rowExpr m cells r i) = if i =? 0 then true else if i =? 1 then b else false.
Proof.
  intros m cells x r b h i. unfold rowExpr. rewrite eval_mux, (doneBit h). cbn [done].
  destruct (i =? 0), (i =? 1); try reflexivity. exact (answerBit h).
Qed.

Theorem step_encodes : forall m cells x r c, Encodes m cells x r c -> 0 < cells ->
  Encodes m (cells-1) x (stepExprs m cells r) (Window.next m (cells-1) c).
Proof.
  intros m cells x r [b|c] h hk.
  - constructor.
    + rewrite step_ref by (unfold width; lia). rewrite (row_halt m cells x r b h). reflexivity.
    + rewrite step_ref by (unfold width; lia). rewrite (row_halt m cells x r b h). reflexivity.
    + intros lane hl. rewrite step_ref by (unfold width; lia).
      rewrite (row_halt m cells x r b h).
      assert (h0 : (2+lane =? 0) = false) by (apply Nat.eqb_neq; lia).
      assert (h1 : (2+lane =? 1) = false) by (apply Nat.eqb_neq; lia).
      rewrite h0,h1. unfold Window.next,scanned,bit. destruct (lane =? 0); reflexivity.
    + intros q hq. rewrite step_ref by (unfold width; lia).
      rewrite (row_halt m cells x r b h).
      assert (h0 : (4+q =? 0) = false) by (apply Nat.eqb_neq; lia).
      assert (h1 : (4+q =? 1) = false) by (apply Nat.eqb_neq; lia).
      rewrite h0,h1. reflexivity.
    + intros side cell lane hc hl. unfold tapeRef.
      rewrite step_ref by (apply rowIndex_lt; assumption).
      rewrite (row_halt m cells x r b h).
      assert (h0 : (4+length (program m)+(if side then 2*(cells-1) else 0)+2*cell+lane =? 0) = false)
        by (apply Nat.eqb_neq; destruct side; lia).
      assert (h1 : (4+length (program m)+(if side then 2*(cells-1) else 0)+2*cell+lane =? 1) = false)
        by (apply Nat.eqb_neq; destruct side; lia).
      rewrite h0,h1. unfold Window.next,tape,bit. destruct (lane =? 0); reflexivity.
  - assert (hs : Window.next m (cells-1) (inr c) =
      match instruction m (state c) (tapeHead c) with
      | halt b => inl b
      | move q s d => inr (Window.window (cells-1) (moveHead c q s d)) end).
    { unfold Window.next,step. destruct (instruction m (state c) (tapeHead c)); reflexivity. }
    constructor.
    + rewrite step_ref by (unfold width; lia). rewrite (row_live m cells x r c h),hs.
      destruct (instruction m (state c) (tapeHead c)); reflexivity.
    + rewrite step_ref by (unfold width; lia). rewrite (row_live m cells x r c h),hs.
      destruct (instruction m (state c) (tapeHead c)); reflexivity.
    + intros lane hl. rewrite step_ref by (unfold width; lia).
      rewrite (row_live m cells x r c h),hs.
      assert (h0 : (2+lane =? 0) = false) by (apply Nat.eqb_neq; lia).
      assert (h1 : (2+lane =? 1) = false) by (apply Nat.eqb_neq; lia).
      assert (h4 : (2+lane <? 4) = true) by (apply Nat.ltb_lt; lia).
      destruct (instruction m (state c) (tapeHead c)) as [b|q s d].
      * unfold instructionBit. rewrite h0,h1. unfold eval,scanned,bit. destruct (lane =? 0); reflexivity.
      * cbn [instructionBit]. unfold movedBit. rewrite h0,h1,h4.
        replace (2+lane-2) with lane by lia.
        change (eval x (match d with
          | stay => symbolBit s lane
          | left => tapeRef (length (program m)) cells r false 0 lane
          | right => tapeRef (length (program m)) cells r true 0 lane end) =
          bit (tapeHead (moveHead c q s d)) lane).
        rewrite moved_head. destruct d; [apply (tapeBits h)|apply (tapeBits h)|reflexivity]; lia.
    + intros q hq. rewrite step_ref by (unfold width; lia).
      rewrite (row_live m cells x r c h),hs.
      assert (h0 : (4+q =? 0) = false) by (apply Nat.eqb_neq; lia).
      assert (h1 : (4+q =? 1) = false) by (apply Nat.eqb_neq; lia).
      assert (h4 : (4+q <? 4) = false) by (apply Nat.ltb_ge; lia).
      assert (hM : (4+q <? 4+length (program m)) = true) by (apply Nat.ltb_lt; lia).
      destruct (instruction m (state c) (tapeHead c)) as [b|q' s d].
      * unfold instructionBit. rewrite h0,h1. reflexivity.
      * cbn [instructionBit]. unfold movedBit. rewrite h0,h1,h4,hM.
        cbn [eval stateBit Window.window state]. rewrite moved_state.
        replace (4+q-4) with q by lia. apply Nat.eqb_sym.
    + intros side cell lane hc hl. unfold tapeRef.
      rewrite step_ref by (apply rowIndex_lt; assumption).
      rewrite (row_live m cells x r c h),hs.
      destruct (instruction m (state c) (tapeHead c)) as [b|q s d].
      * assert (h0 : (4+length (program m)+(if side then 2*(cells-1) else 0)+2*cell+lane =? 0) = false)
          by (apply Nat.eqb_neq; destruct side; lia).
        assert (h1 : (4+length (program m)+(if side then 2*(cells-1) else 0)+2*cell+lane =? 1) = false)
          by (apply Nat.eqb_neq; destruct side; lia).
        unfold instructionBit. rewrite h0,h1. unfold eval,tape,bit. destruct (lane =? 0); reflexivity.
      * cbn [instructionBit]. rewrite moved_tape_eval with (c:=c) by assumption.
        rewrite tape_window by assumption. reflexivity.
Qed.

Lemma getD_map_bounded : forall (A B : Type) (l : list A) (f : A -> B) i da db,
  i < length l -> nth i (map f l) db = f (nth i l da).
Proof.
  intros A B l f; induction l; intros [] da db hi; simpl in *; try lia; auto.
  apply IHl. lia.
Qed.
Lemma getD_ge : forall (A : Type) (l : list A) i d,
  length l <= i -> nth i l d = d.
Proof.
  intros A l; induction l; intros [] d hi; simpl in *; try lia; auto.
  apply IHl. lia.
Qed.

Lemma inputSymbolBit_eval : forall x cell lane,
  eval x (inputSymbolBit (length x) cell lane) = bit (nth cell (map ofBool x) blank) lane.
Proof.
  intros x cell lane. unfold inputSymbolBit. destruct (cell <? length x) eqn:hc.
  - apply Nat.ltb_lt in hc. rewrite getD_map_bounded with (da:=false) by assumption.
    unfold wire in *. destruct (lane =? 0) eqn:hl.
    + cbn [eval]. unfold wire,bit. rewrite hl. destruct (nth cell x false); reflexivity.
    + cbn [neg eval]. unfold wire,bit. rewrite hl. destruct (nth cell x false); reflexivity.
  - apply Nat.ltb_ge in hc. rewrite getD_ge by (rewrite length_map; assumption).
    unfold bit. destruct (lane =? 0); reflexivity.
Qed.
Lemma initial_head : forall x,
  tapeHead (initial x) = nth 0 (map ofBool x) blank.
Proof. intros []; reflexivity. Qed.
Lemma initial_tape : forall x side cell,
  tape (inr (initial x)) side cell = if side then nth (cell+1) (map ofBool x) blank else blank.
Proof.
  intros [] [] cell; rewrite ?Nat.add_1_r; cbn [initial initialSymbols tape];
    rewrite ?nth_nil; reflexivity.
Qed.
Lemma encodes_window : forall m cells x r c, Encodes m cells x r (inr c) ->
  Encodes m cells x r (inr (Window.window cells c)).
Proof.
  intros m cells x r c h. constructor; try exact (doneBit h); try exact (answerBit h).
  - exact (headBits h).
  - exact (stateBits h).
  - intros. rewrite tape_window by assumption. apply (tapeBits h); assumption.
Qed.

Lemma initial_state : forall x, state (initial x) = 0.
Proof. intros []; reflexivity. Qed.

Theorem initial_encodes : forall m cells x,
  Encodes m cells x (initialExprs m (length x) cells) (inr (initial x)).
Proof.
  intros m cells x.
  assert (hr : forall i, i < width (length (program m)) cells ->
    eval x (ref (initialExprs m (length x) cells) i) =
      eval x (if i <? 2 then lit false
        else if i <? 4 then inputSymbolBit (length x) 0 (i-2)
        else if i <? 4+length (program m) then lit (i =? 4)
        else let j := i-(4+length (program m)) in
          if j <? 2*cells then lit false
          else inputSymbolBit (length x) ((j-2*cells)/2+1) ((j-2*cells) mod 2))).
  { intros. apply ref_range. assumption. }
  constructor.
  - rewrite hr by (unfold width; lia). reflexivity.
  - rewrite hr by (unfold width; lia). reflexivity.
  - intros lane hl. rewrite hr by (unfold width; lia).
    assert (h2 : (2+lane <? 2) = false) by (apply Nat.ltb_ge; lia).
    assert (h4 : (2+lane <? 4) = true) by (apply Nat.ltb_lt; lia).
    rewrite h2,h4. replace (2+lane-2) with lane by lia.
    rewrite inputSymbolBit_eval. unfold scanned. rewrite initial_head. reflexivity.
  - intros q hq. rewrite hr by (unfold width; lia).
    assert (h2 : (4+q <? 2) = false) by (apply Nat.ltb_ge; lia).
    assert (h4 : (4+q <? 4) = false) by (apply Nat.ltb_ge; lia).
    assert (hM : (4+q <? 4+length (program m)) = true) by (apply Nat.ltb_lt; lia).
    rewrite h2,h4,hM. cbn [eval stateBit]. rewrite initial_state.
    destruct q; reflexivity.
  - intros side cell lane hc hl. unfold tapeRef. rewrite hr by (apply rowIndex_lt; assumption).
    rewrite initial_tape.
    set (i := 4+length (program m)+(if side then 2*cells else 0)+2*cell+lane).
    assert (h2 : (i <? 2) = false) by (apply Nat.ltb_ge; unfold i; destruct side; lia).
    assert (h4 : (i <? 4) = false) by (apply Nat.ltb_ge; unfold i; destruct side; lia).
    assert (hM : (i <? 4+length (program m)) = false)
      by (apply Nat.ltb_ge; unfold i; destruct side; lia).
    fold i. rewrite h2,h4,hM. cbn zeta.
    destruct side.
    + assert (hj : i-(4+length (program m)) = 2*cells+(2*cell+lane)) by (unfold i; lia).
      rewrite hj.
      assert (hb : (2*cells+(2*cell+lane) <? 2*cells) = false) by (apply Nat.ltb_ge; lia).
      rewrite hb. replace (2*cells+(2*cell+lane)-2*cells) with (2*cell+lane) by lia.
      rewrite div2,mod2 by assumption. apply inputSymbolBit_eval.
    + assert (hj : i-(4+length (program m)) = 2*cell+lane) by (unfold i; lia).
      rewrite hj.
      assert (hb : (2*cell+lane <? 2*cells) = true) by (apply Nat.ltb_lt; lia).
      rewrite hb. unfold bit. destruct (lane =? 0); reflexivity.
Qed.

Theorem compileMany_encodes : forall m cells x es c, 0 < length x ->
  (forall a, In a es -> Bounded (length x) a) -> Encodes m cells x es c ->
  Encodes m cells (wires x (fst (compileMany (length x) es)))
    (map input (snd (compileMany (length x) es))) c.
Proof.
  intros m cells x es c hx hb h. pose proof (compileMany_correct es x hx hb) as he.
  assert (hr : forall i, eval (wires x (fst (compileMany (length x) es)))
    (ref (map input (snd (compileMany (length x) es))) i) = eval x (ref es i)).
  { intros i. rewrite !eval_ref,map_map.
    change (nth i (map (wire (wires x (fst (compileMany (length x) es))))
      (snd (compileMany (length x) es))) false = nth i (map (eval x) es) false).
    rewrite he. reflexivity. }
  constructor.
  - rewrite hr. exact (doneBit h).
  - rewrite hr. exact (answerBit h).
  - intros. rewrite hr. apply (headBits h); assumption.
  - intros. rewrite hr. apply (stateBits h); assumption.
  - intros. unfold tapeRef. rewrite hr. apply (tapeBits h); assumption.
Qed.

Lemma finish_correct : forall x refs, output x (finish (length x) refs) = wire x (nth 1 refs 0).
Proof.
  intros. unfold finish,output. cbn [wires]. rewrite last_last,wire_append_self.
  destruct (wire x (nth 1 refs 0)); reflexivity.
Qed.

Theorem compileRows_correct : forall m t cells x refs c, 0 < length x ->
  (forall i, In i refs -> i < length x) -> 2 <= length refs -> t <= cells ->
  Encodes m cells x (map input refs) c ->
  output x (compileRows m t cells (length x) refs) = answer (Window.runWindow m t cells c).
Proof.
  intros m t. induction t; intros cells x refs c hx hw hlen ht h.
  - cbn [compileRows Window.runWindow]. rewrite finish_correct.
    pose proof (answerBit h) as ha. rewrite eval_ref,map_map in ha.
    change (nth 1 (map (wire x) refs) false = answer c) in ha.
    rewrite getD_map_bounded with (da:=0) in ha by lia. exact ha.
  - set (es := stepExprs m cells (map input refs)).
    assert (hb : forall e, In e es -> Bounded (length x) e).
    { apply stepExprs_bounded. intros e he. apply in_map_iff in he.
      destruct he as [i [<- hi]]. apply hw. exact hi. }
    pose proof (step_encodes m cells x (map input refs) c h ltac:(lia)) as hs.
    pose proof (compileMany_encodes m (cells-1) x es (Window.next m (cells-1) c) hx hb hs) as hc.
    pose proof (compileMany_WF es (length x) hx hb) as hjs.
    pose proof (compileMany_outputs_length es (length x)) as hl.
    cbn [compileRows]. fold es. destruct (compileMany (length x) es) as [A js] eqn:he.
    cbn [fst snd] in hc,hjs,hl. destruct hjs as [_ hjs].
    assert (hy : length (wires x A) = length x + length A) by apply wires_length.
    assert (hjl : 2 <= length js).
    { rewrite hl. unfold es,stepExprs. rewrite length_map,length_seq. unfold width. lia. }
    unfold output. rewrite wires_append. rewrite <- hy.
    change (output (wires x A) (compileRows m t (cells-1) (length (wires x A)) js) =
      answer (Window.runWindow m t (cells-1) (Window.next m (cells-1) c))).
    apply IHt; try exact hc; try exact hjl; try lia.
    intros i hi. rewrite hy. apply hjs. exact hi.
Qed.

Theorem simCircuit_correct : forall m p x, 0 < length x -> forall t b,
  Run m (initial x) t b -> t <= evalPoly p (length x) ->
  output x (simCircuit m p (length x)) = b.
Proof.
  intros m p x hx t b hr ht.
  set (clock := evalPoly p (length x)). set (cells := length x+clock+1).
  set (es := initialExprs m (length x) cells).
  pose proof (initialExprs_bounded m (length x) cells) as hb.
  pose proof (encodes_window m cells x es (initial x) (initial_encodes m cells x)) as hi.
  pose proof (compileMany_encodes m cells x es (inr (Window.window cells (initial x))) hx hb hi) as hc.
  pose proof (compileMany_WF es (length x) hx hb) as hjs.
  pose proof (compileMany_outputs_length es (length x)) as hl.
  unfold simCircuit. fold clock cells es.
  destruct (compileMany (length x) es) as [A js] eqn:he. cbn [fst snd] in hc,hjs,hl.
  destruct hjs as [_ hjs].
  assert (hy : length (wires x A) = length x+length A) by apply wires_length.
  assert (hjl : 2 <= length js).
  { rewrite hl. unfold es,initialExprs. rewrite length_map,length_seq. unfold width. lia. }
  pose proof (compileRows_correct m clock cells (wires x A) js
    (inr (Window.window cells (initial x))) ltac:(rewrite hy; lia)
    ltac:(intros; rewrite hy; apply hjs; assumption) hjl ltac:(unfold cells; lia) hc) as ho.
  rewrite (Window.runWindow_correct m (initial x) t b hr clock cells ht ltac:(unfold cells; lia)) in ho.
  unfold output. rewrite wires_append, <- hy. exact ho.
Qed.

(** Shared local tableaux certify the circuit answer and fit its cell budget. *)
Theorem simCircuit_correct_of_localTrace : forall m p x trace b,
  0 < length x -> hd_error trace = Some (initial x) ->
  length trace <= evalPoly p (length x) -> Tableau.localTrace m b trace ->
  output x (simCircuit m p (length x)) = b /\
    forall d, In d trace -> Tableau.span d <= length x + evalPoly p (length x) + 1.
Proof.
  intros m p x trace b hx hstart ht hlocal. split.
  - apply (simCircuit_correct m p x hx (length trace) b); [|exact ht].
    apply (proj1 (Tableau.localTrace_iff_run m (initial x) (length trace) b)).
    exists trace. repeat split; assumption || reflexivity.
  - intros d hd. exact (Tableau.bounded_initial_span m x (evalPoly p (length x))
      b trace d hstart ht hlocal hd).
Qed.

Theorem machine_inPPoly : forall P : ClassP, InPPoly (p_language P).
Proof.
  intros P. exists (simulationPolynomial (p_machine P) (p_bound P)). intros n hn.
  exists (simCircuit (p_machine P) (p_bound P) n). split; [apply simCircuit_polynomial_size|].
  split; [apply simCircuit_WF; assumption|]. intros x hx. subst n.
  destruct (p_terminates P x) as [t [b [ht hr]]].
  rewrite (simCircuit_correct (p_machine P) (p_bound P) x hn t b hr ht).
  pose proof (p_correct P x t b hr) as hc.
  destruct b, (p_language P x); try reflexivity; destruct hc as [ha hb];
    first [pose proof (ha eq_refl) as hf | pose proof (hb eq_refl) as hf]; discriminate.
Qed.

Theorem pSubsetPPoly : PSubsetPPoly.
Proof. intros L [P <-]. apply machine_inPPoly. Qed.

End SimulationCorrectness.
