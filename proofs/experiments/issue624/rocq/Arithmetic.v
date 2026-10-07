From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Export RegisterMachine.
Import ListNotations.

(** Arithmetic expands to the existing charged register compiler. *)
Module Arithmetic.
Import Complexity Machines RegisterMachine.

Definition mulProgram (a b dest : nat) : Program :=
  let counter := subCounter a b dest in
  let scratch := subScratch a b dest in
  sequence (clearRegister counter)
    (sequence (addToProgram a counter scratch)
      (sequence (clearRegister dest) (loop counter (addToProgram b dest scratch)))).
Definition positiveProgram (counter dest : nat) : Program :=
  sequence (clearRegister dest)
    (loop counter (sequence (clearRegister dest) (straight (increment dest 1)))).
Definition ltProgram (a b dest : nat) : Program :=
  let counter := subCounter a b dest in
  sequence (subProgram b a counter) (positiveProgram counter dest).
Definition zeroPairProgram (counter other dest : nat) : Program :=
  sequence (clearRegister dest)
    (sequence (straight (increment dest 1))
      (sequence (loop counter (clearRegister dest)) (loop other (clearRegister dest)))).
Definition eqProgram (a b dest : nat) : Program :=
  let counter := subCounter a b dest in
  sequence (subProgram a b counter)
    (sequence (subProgram b a (counter+3))
      (zeroPairProgram counter (counter+3) dest)).

Theorem arithmetic_scratch : forall a b dest,
  subCounter b a (subCounter a b dest) = subCounter a b dest + 1 /\
  subScratch b a (subCounter a b dest) = subCounter a b dest + 2 /\
  subCounter a b (subCounter a b dest) = subCounter a b dest + 1 /\
  subScratch a b (subCounter a b dest) = subCounter a b dest + 2 /\
  subCounter b a (subCounter a b dest+3) = subCounter a b dest + 4 /\
  subScratch b a (subCounter a b dest+3) = subCounter a b dest + 5.
Proof.
  intros. destruct (subCounter_wider a b dest) as [ha [hb hd]].
  assert (hm : Nat.max a (Nat.max b (subCounter a b dest)) = subCounter a b dest)
    by (rewrite !Nat.max_r; lia).
  assert (hm' : Nat.max b (Nat.max a (subCounter a b dest)) = subCounter a b dest)
    by (rewrite !Nat.max_r; lia).
  assert (hm3 : Nat.max b (Nat.max a (subCounter a b dest+3)) = subCounter a b dest+3)
    by (rewrite !Nat.max_r; lia).
  assert (hc1 : subCounter b a (subCounter a b dest) = subCounter a b dest+1).
  { change (Nat.max b (Nat.max a (subCounter a b dest))+1 = subCounter a b dest+1). rewrite hm'. reflexivity. }
  assert (hc2 : subCounter a b (subCounter a b dest) = subCounter a b dest+1).
  { change (Nat.max a (Nat.max b (subCounter a b dest))+1 = subCounter a b dest+1). rewrite hm. reflexivity. }
  assert (hc3 : subCounter b a (subCounter a b dest+3) = subCounter a b dest+4).
  { change (Nat.max b (Nat.max a (subCounter a b dest+3))+1 = subCounter a b dest+4). rewrite hm3. lia. }
  unfold subScratch. rewrite hc1, hc2, hc3. repeat split; lia.
Qed.

Theorem mulProgram_wellFormed : forall k a b dest,
  subScratch a b dest < k -> b <> dest -> ProgramWellFormed k (mulProgram a b dest).
Proof.
  intros. destruct (subCounter_wider a b dest) as [ha [hb hd]].
  unfold subScratch in *. unfold mulProgram.
  cbn [addToProgram ProgramWellFormed ProgramReadOnly WellFormed ReadOnly].
  repeat split; unfold subScratch; lia.
Qed.
Theorem positiveProgram_wellFormed : forall k counter dest,
  counter < k -> dest < k -> counter <> dest -> ProgramWellFormed k (positiveProgram counter dest).
Proof.
  intros. unfold positiveProgram. cbn [ProgramWellFormed ProgramReadOnly WellFormed ReadOnly].
  repeat split; assumption.
Qed.
Theorem ltProgram_wellFormed : forall k a b dest,
  subCounter a b dest + 2 < k -> ProgramWellFormed k (ltProgram a b dest).
Proof.
  intros. destruct (subCounter_wider a b dest) as [ha [hb hd]].
  destruct (arithmetic_scratch a b dest) as [h1 [h2 rest]].
  unfold ltProgram. split.
  - apply subProgram_wellFormed; [rewrite h2|]; lia.
  - apply positiveProgram_wellFormed; lia.
Qed.
Theorem eqProgram_wellFormed : forall k a b dest,
  subCounter a b dest + 5 < k -> ProgramWellFormed k (eqProgram a b dest).
Proof.
  intros. destruct (subCounter_wider a b dest) as [ha [hb hd]].
  destruct (arithmetic_scratch a b dest) as [h1 [h2 [h3 [h4 [h5 h6]]]]].
  unfold eqProgram. split; [apply subProgram_wellFormed; [rewrite h4|]; lia|].
  split; [apply subProgram_wellFormed; [rewrite h6|]; lia|].
  cbn [zeroPairProgram ProgramWellFormed ProgramReadOnly WellFormed]. repeat split; lia.
Qed.

Ltac register_cases :=
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] => destruct (a =? b) eqn:?
  end;
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  end;
  repeat match goal with
  | H : ?a = ?b |- _ => first [is_var a; subst a | is_var b; subst b]
  end;
  cbn [orb andb] in *; try congruence; try lia; try nia; try reflexivity.

Ltac order_cases :=
  repeat match goal with
  | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
  | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
  end.

Theorem loopRun_addTo : forall counter source dest scratch,
  counter <> source -> counter <> dest -> counter <> scratch ->
  source <> dest -> source <> scratch -> dest <> scratch -> forall n st,
  counter < length (regs st) -> source < length (regs st) ->
  dest < length (regs st) -> scratch < length (regs st) ->
  registerAt counter st = n -> registerAt scratch st = 0 -> forall slot,
  registerAt slot (loopRun counter (programRun (addToProgram source dest scratch)) n st) =
    if (slot =? counter) || (slot =? scratch) then 0 else
    if slot =? dest then registerAt dest st + n * registerAt source st else registerAt slot st.
Proof.
  intros counter source dest scratch hcs hcd hcc hsd hsc hdc n.
  induction n; intros st hc hs hd ht hn hz slot.
  - cbn [loopRun Nat.mul Nat.add]. register_cases.
  - set (lower := putRegister counter n st).
    set (next := programRun (addToProgram source dest scratch) lower).
    assert (hl : length (regs lower) = length (regs st)) by apply putRegister_length.
    assert (hlen : length (regs next) = length (regs st)) by
      (unfold next; rewrite programRun_regs_length; exact hl).
    assert (hh : forall i, registerAt i next =
      if i =? scratch then 0 else if i =? dest then registerAt dest st + registerAt source st else
      if i =? counter then n else registerAt i st).
    { intros i. unfold next. rewrite addToProgram_registers by lia.
      assert (hdd : registerAt dest lower = registerAt dest st) by
        (unfold lower; apply registerAt_putRegister_other; congruence).
      assert (hss : registerAt source lower = registerAt source st) by
        (unfold lower; apply registerAt_putRegister_other; congruence).
      rewrite hdd, hss. destruct (i =? scratch); [reflexivity|].
      destruct (i =? dest); [reflexivity|]. destruct (i =? counter) eqn:he.
      - apply Nat.eqb_eq in he. subst i. unfold lower. apply registerAt_putRegister; exact hc.
      - apply Nat.eqb_neq in he. unfold lower. apply registerAt_putRegister_other; exact he. }
    assert (hcn : registerAt counter next = n) by (rewrite hh; register_cases).
    assert (hsz : registerAt scratch next = 0) by (rewrite hh, Nat.eqb_refl; reflexivity).
    cbn [loopRun]. fold lower next.
    rewrite (IHn next ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) hcn hsz slot).
    rewrite !hh. register_cases.
Qed.

Theorem mulProgram_registers : forall a b dest st,
  subScratch a b dest < length (regs st) -> b <> dest -> forall slot,
  registerAt slot (programRun (mulProgram a b dest) st) =
    if (slot =? subCounter a b dest) || (slot =? subScratch a b dest) then 0 else
    if slot =? dest then registerAt a st * registerAt b st else registerAt slot st.
Proof.
  intros a b dest st hk hbd slot.
  set (counter := subCounter a b dest). set (scratch := subScratch a b dest).
  destruct (subCounter_wider a b dest) as [ha [hb hd]].
  change (a < counter) in ha. change (b < counter) in hb. change (dest < counter) in hd.
  assert (hc : counter < scratch) by (unfold scratch, subScratch; fold counter; lia).
  change (scratch < length (regs st)) in hk.
  set (initial := putRegister counter 0 st).
  assert (hil : length (regs initial) = length (regs st)) by apply putRegister_length.
  set (captured := programRun (addToProgram a counter scratch) initial).
  set (copied := putRegister dest 0 captured).
  assert (hlen : length (regs copied) = length (regs st)) by
    (unfold copied, captured, initial; rewrite putRegister_length, programRun_regs_length, putRegister_length; reflexivity).
  assert (hcap : forall i, registerAt i captured =
    if i =? scratch then 0 else if i =? counter then registerAt a st else registerAt i st).
  { intros i. unfold captured. rewrite addToProgram_registers by (try rewrite hil; lia).
    assert (has : registerAt a initial = registerAt a st) by
      (unfold initial; apply registerAt_putRegister_other; lia).
    assert (hc0 : registerAt counter initial = 0) by (unfold initial; apply registerAt_putRegister; lia).
    rewrite has, hc0. cbn [Nat.add]. destruct (i =? scratch); [reflexivity|].
    destruct (i =? counter) eqn:he; [reflexivity|]. apply Nat.eqb_neq in he.
    unfold initial. apply registerAt_putRegister_other; exact he. }
  assert (hcopy : forall i, registerAt i copied =
    if i =? dest then 0 else if i =? scratch then 0 else if i =? counter then registerAt a st else registerAt i st).
  { intros i. unfold copied. destruct (i =? dest) eqn:he.
    - apply Nat.eqb_eq in he. subst i. apply registerAt_putRegister.
      unfold captured, initial. rewrite programRun_regs_length, putRegister_length. lia.
    - apply Nat.eqb_neq in he. rewrite registerAt_putRegister_other by exact he. apply hcap. }
  change (registerAt slot (loopRun counter (programRun (addToProgram b dest scratch))
    (registerAt counter copied) copied) =
    if (slot =? counter) || (slot =? scratch) then 0 else
    if slot =? dest then registerAt a st * registerAt b st else registerAt slot st).
  rewrite loopRun_addTo by (try lia; try reflexivity; rewrite hcopy; register_cases).
  rewrite !hcopy. register_cases.
Qed.
Theorem mulProgram_out : forall a b dest st,
  out (programRun (mulProgram a b dest) st) = out st.
Proof.
  intros. unfold mulProgram. cbn [programRun].
  rewrite loopRun_out by apply addToProgram_out.
  change (out (programRun (addToProgram a (subCounter a b dest) (subScratch a b dest))
    (putRegister (subCounter a b dest) 0 st)) = out st).
  rewrite addToProgram_out. reflexivity.
Qed.
Theorem mulProgram_reaches : forall x k a b dest st,
  length (regs st) = k -> subScratch a b dest < k -> b <> dest ->
  exists c, Reaches (compileProgram k (mulProgram a b dest)) (encode 0 x st)
    (programCost x (mulProgram a b dest) st) c /\
    Similar (encode (length (program (compileProgram k (mulProgram a b dest)))) x
      (programRun (mulProgram a b dest) st)) c.
Proof. intros. apply compileProgram_reaches; [apply mulProgram_wellFormed; assumption|assumption]. Qed.

Theorem loopRun_constant : forall counter dest value (body : State -> State),
  counter <> dest -> (forall s, length (regs (body s)) = length (regs s)) ->
  (forall s, dest < length (regs s) -> forall i,
    registerAt i (body s) = if i =? dest then value else registerAt i s) ->
  forall n st, counter < length (regs st) -> dest < length (regs st) ->
  registerAt counter st = n -> forall slot,
  registerAt slot (loopRun counter body n st) =
    if slot =? counter then 0 else if slot =? dest then
      (if n =? 0 then registerAt dest st else value) else registerAt slot st.
Proof.
  intros counter dest value body hcd hr hb n. induction n; intros st hc hd hn slot.
  - cbn [loopRun]. register_cases.
  - set (lower := putRegister counter n st). set (next := body lower).
    assert (hl : length (regs lower) = length (regs st)) by apply putRegister_length.
    assert (hlen : length (regs next) = length (regs st)) by (unfold next; rewrite hr; exact hl).
    assert (hh : forall i, registerAt i next =
      if i =? dest then value else if i =? counter then n else registerAt i st).
    { intros i. unfold next. rewrite hb by lia.
      destruct (i =? dest); [reflexivity|]. destruct (i =? counter) eqn:he.
      - apply Nat.eqb_eq in he. subst i. unfold lower. apply registerAt_putRegister; exact hc.
      - apply Nat.eqb_neq in he. unfold lower. apply registerAt_putRegister_other; exact he. }
    assert (hcn : registerAt counter next = n) by (rewrite hh; register_cases).
    cbn [loopRun]. fold lower next. rewrite IHn by (try lia; exact hcn).
    rewrite !hh. register_cases.
Qed.

Theorem setFlag_registers : forall dest st, dest < length (regs st) -> forall slot,
  registerAt slot (programRun (sequence (clearRegister dest) (straight (increment dest 1))) st) =
    if slot =? dest then 1 else registerAt slot st.
Proof.
  intros dest st hd slot. destruct (slot =? dest) eqn:he.
  - apply Nat.eqb_eq in he. subst slot. cbn [programRun].
    rewrite incrementRegs_registerAt by (rewrite putRegister_length; exact hd).
    rewrite registerAt_putRegister by exact hd. reflexivity.
  - apply Nat.eqb_neq in he. apply programRun_readOnly.
    cbn [ProgramReadOnly ReadOnly]. split; exact he.
Qed.
Theorem positiveProgram_registers : forall counter dest st,
  counter < length (regs st) -> dest < length (regs st) -> counter <> dest -> forall slot,
  registerAt slot (programRun (positiveProgram counter dest) st) =
    if slot =? counter then 0 else if slot =? dest then
      (if registerAt counter st =? 0 then 0 else 1) else registerAt slot st.
Proof.
  intros counter dest st hc hd hcd slot. set (initial := putRegister dest 0 st).
  assert (hl : length (regs initial) = length (regs st)) by apply putRegister_length.
  change (registerAt slot (loopRun counter
    (programRun (sequence (clearRegister dest) (straight (increment dest 1))))
    (registerAt counter initial) initial) =
    if slot =? counter then 0 else if slot =? dest then
      (if registerAt counter st =? 0 then 0 else 1) else registerAt slot st).
  rewrite (loopRun_constant counter dest 1 _ hcd (programRun_regs_length _)
    (setFlag_registers dest) _ initial ltac:(lia) ltac:(lia) eq_refl slot).
  assert (hcc : registerAt counter initial = registerAt counter st) by
    (unfold initial; apply registerAt_putRegister_other; exact hcd).
  assert (hdd : registerAt dest initial = 0) by
    (unfold initial; apply registerAt_putRegister; exact hd).
  rewrite hcc, hdd. destruct (slot =? counter); [reflexivity|].
  destruct (slot =? dest) eqn:he; [reflexivity|]. apply Nat.eqb_neq in he.
  unfold initial. apply registerAt_putRegister_other; exact he.
Qed.
Theorem positiveProgram_out : forall counter dest st,
  out (programRun (positiveProgram counter dest) st) = out st.
Proof.
  intros. unfold positiveProgram. cbn [programRun].
  rewrite loopRun_out by (intros; reflexivity). reflexivity.
Qed.
Theorem ltProgram_registers : forall a b dest st,
  subCounter a b dest+2 < length (regs st) -> forall slot,
  registerAt slot (programRun (ltProgram a b dest) st) =
    if (subCounter a b dest <=? slot) && (slot <=? subCounter a b dest+2) then 0 else
    if slot =? dest then (if registerAt a st <? registerAt b st then 1 else 0) else registerAt slot st.
Proof.
  intros a b dest st hk slot. set (counter := subCounter a b dest).
  set (diff := programRun (subProgram b a counter) st).
  destruct (subCounter_wider a b dest) as [ha [hb hd]].
  change (a < counter) in ha. change (b < counter) in hb. change (dest < counter) in hd.
  destruct (arithmetic_scratch a b dest) as [h1 [h2 rest]]. fold counter in h1, h2, hk.
  assert (hl : length (regs diff) = length (regs st)) by apply programRun_regs_length.
  assert (hh : forall i, registerAt i diff =
    if (i =? counter+1) || (i =? counter+2) then 0 else
    if i =? counter then registerAt b st - registerAt a st else registerAt i st).
  { intros. unfold diff. rewrite subProgram_registers by (rewrite ?h2; lia).
    rewrite h1, h2. reflexivity. }
  change (registerAt slot (programRun (positiveProgram counter dest) diff) =
    if (counter <=? slot) && (slot <=? counter+2) then 0 else
    if slot =? dest then (if registerAt a st <? registerAt b st then 1 else 0) else registerAt slot st).
  assert (hv : registerAt counter diff = registerAt b st - registerAt a st)
    by (rewrite hh; register_cases).
  rewrite positiveProgram_registers by lia. rewrite hv, hh.
  destruct (counter <=? slot) eqn:hle; destruct (slot <=? counter+2) eqn:hle';
    destruct (registerAt a st <? registerAt b st) eqn:hlt;
    order_cases; register_cases.
Qed.
Theorem ltProgram_out : forall a b dest st, out (programRun (ltProgram a b dest) st) = out st.
Proof. intros. unfold ltProgram. cbn [programRun]. rewrite positiveProgram_out, subProgram_out. reflexivity. Qed.
Theorem ltProgram_reaches : forall x k a b dest st,
  length (regs st) = k -> subCounter a b dest+2 < k ->
  exists c, Reaches (compileProgram k (ltProgram a b dest)) (encode 0 x st)
    (programCost x (ltProgram a b dest) st) c /\
    Similar (encode (length (program (compileProgram k (ltProgram a b dest)))) x
      (programRun (ltProgram a b dest) st)) c.
Proof. intros. apply compileProgram_reaches; [apply ltProgram_wellFormed; assumption|assumption]. Qed.

Theorem clearLoop_registers : forall counter dest st,
  counter < length (regs st) -> dest < length (regs st) -> counter <> dest -> forall slot,
  registerAt slot (programRun (loop counter (clearRegister dest)) st) =
    if slot =? counter then 0 else if slot =? dest then
      (if registerAt counter st =? 0 then registerAt dest st else 0) else registerAt slot st.
Proof.
  intros counter dest st hc hd hcd slot.
  refine (loopRun_constant counter dest 0 (programRun (clearRegister dest)) hcd
    (programRun_regs_length _) _ _ st hc hd eq_refl slot).
  intros s hs i. cbn [programRun]. destruct (i =? dest) eqn:he.
  - apply Nat.eqb_eq in he. subst i. apply registerAt_putRegister; exact hs.
  - apply Nat.eqb_neq in he. apply registerAt_putRegister_other; exact he.
Qed.

Theorem zeroPairProgram_registers : forall counter other dest st,
  counter < length (regs st) -> other < length (regs st) -> dest < length (regs st) ->
  counter <> other -> counter <> dest -> other <> dest -> forall slot,
  registerAt slot (programRun (zeroPairProgram counter other dest) st) =
    if (slot =? counter) || (slot =? other) then 0 else if slot =? dest then
      (if (registerAt counter st =? 0) && (registerAt other st =? 0) then 1 else 0) else registerAt slot st.
Proof.
  intros counter other dest st hc ho hd hco hcd hod slot.
  set (flagged := programRun (sequence (clearRegister dest) (straight (increment dest 1))) st).
  set (first := programRun (loop counter (clearRegister dest)) flagged).
  assert (hlf : length (regs flagged) = length (regs st)) by apply programRun_regs_length.
  assert (hll : length (regs first) = length (regs st)) by
    (unfold first; rewrite programRun_regs_length; exact hlf).
  assert (hf : forall i, registerAt i flagged = if i =? dest then 1 else registerAt i st)
    by (intros; apply setFlag_registers; exact hd).
  assert (hv1 : registerAt counter flagged = registerAt counter st) by (rewrite hf; register_cases).
  assert (hh : forall i, registerAt i first = if i =? counter then 0 else if i =? dest then
    (if registerAt counter st =? 0 then 1 else 0) else registerAt i flagged).
  { intros. unfold first. rewrite clearLoop_registers by lia.
    rewrite hv1, (hf dest), Nat.eqb_refl. reflexivity. }
  assert (hv2 : registerAt other first = registerAt other st) by (rewrite hh, hf; register_cases).
  assert (hv3 : registerAt dest first = if registerAt counter st =? 0 then 1 else 0)
    by (rewrite hh; register_cases).
  change (registerAt slot (programRun (loop other (clearRegister dest)) first) =
    if (slot =? counter) || (slot =? other) then 0 else if slot =? dest then
      (if (registerAt counter st =? 0) && (registerAt other st =? 0) then 1 else 0) else registerAt slot st).
  rewrite clearLoop_registers by lia. rewrite hv2, hv3, hh, hf. register_cases.
Qed.
Theorem zeroPairProgram_out : forall counter other dest st,
  out (programRun (zeroPairProgram counter other dest) st) = out st.
Proof.
  intros. unfold zeroPairProgram. cbn [programRun].
  rewrite loopRun_out by (intros; reflexivity).
  rewrite loopRun_out by (intros; reflexivity). reflexivity.
Qed.

Theorem eqProgram_registers : forall a b dest st,
  subCounter a b dest+5 < length (regs st) -> forall slot,
  registerAt slot (programRun (eqProgram a b dest) st) =
    if (subCounter a b dest <=? slot) && (slot <=? subCounter a b dest+5) then 0 else
    if slot =? dest then (if registerAt a st =? registerAt b st then 1 else 0) else registerAt slot st.
Proof.
  intros a b dest st hk slot. set (counter := subCounter a b dest).
  set (diff1 := programRun (subProgram a b counter) st).
  set (diff2 := programRun (subProgram b a (counter+3)) diff1).
  set (flagged := programRun (sequence (clearRegister dest) (straight (increment dest 1))) diff2).
  set (first := programRun (loop counter (clearRegister dest)) flagged).
  destruct (subCounter_wider a b dest) as [ha [hb hd]].
  change (a < counter) in ha. change (b < counter) in hb. change (dest < counter) in hd.
  destruct (arithmetic_scratch a b dest) as [_ [_ [he1 [he2 [he3 he4]]]]].
  fold counter in he1, he2, he3, he4, hk.
  assert (hl1 : length (regs diff1) = length (regs st)) by apply programRun_regs_length.
  assert (hl2 : length (regs diff2) = length (regs st)) by
    (unfold diff2; rewrite programRun_regs_length; exact hl1).
  assert (hlf : length (regs flagged) = length (regs st)) by
    (unfold flagged; rewrite programRun_regs_length; exact hl2).
  assert (hll : length (regs first) = length (regs st)) by
    (unfold first; rewrite programRun_regs_length; exact hlf).
  assert (h1 : forall i, registerAt i diff1 =
    if (i =? counter+1) || (i =? counter+2) then 0 else
    if i =? counter then registerAt a st - registerAt b st else registerAt i st).
  { intros. unfold diff1. rewrite subProgram_registers by (rewrite ?he2; lia).
    rewrite he1, he2. reflexivity. }
  assert (h2 : forall i, registerAt i diff2 =
    if (i =? counter+4) || (i =? counter+5) then 0 else
    if i =? counter+3 then registerAt b st - registerAt a st else registerAt i diff1).
  { intros. unfold diff2. rewrite subProgram_registers by (try rewrite he4, hl1; lia).
    rewrite he3, he4, (h1 b), (h1 a).
    assert (hba : (b =? counter+1) || (b =? counter+2) = false) by register_cases.
    assert (haa : (a =? counter+1) || (a =? counter+2) = false) by register_cases.
    assert (hbc : (b =? counter) = false) by (apply Nat.eqb_neq; lia).
    assert (hac : (a =? counter) = false) by (apply Nat.eqb_neq; lia).
    rewrite hba, haa, hbc, hac. reflexivity. }
  assert (hf : forall i, registerAt i flagged = if i =? dest then 1 else registerAt i diff2)
    by (intros; apply setFlag_registers; lia).
  assert (hv1 : registerAt counter flagged = registerAt a st - registerAt b st)
    by (rewrite hf, h2, h1; register_cases).
  assert (hfirst : forall i, registerAt i first =
    if i =? counter then 0 else if i =? dest then
      (if registerAt a st - registerAt b st =? 0 then 1 else 0) else registerAt i flagged).
  { intros. unfold first. rewrite clearLoop_registers by lia.
    rewrite hv1, (hf dest), Nat.eqb_refl. reflexivity. }
  assert (hv2 : registerAt (counter+3) first = registerAt b st - registerAt a st)
    by (rewrite hfirst, hf, h2; register_cases).
  change (registerAt slot (programRun (loop (counter+3) (clearRegister dest)) first) =
    if (counter <=? slot) && (slot <=? counter+5) then 0 else
    if slot =? dest then (if registerAt a st =? registerAt b st then 1 else 0) else registerAt slot st).
  rewrite clearLoop_registers by lia. rewrite hv2, !hfirst, !hf, !h2, !h1.
  destruct (counter <=? slot) eqn:hle; destruct (slot <=? counter+5) eqn:hle';
    order_cases; register_cases.
Qed.
Theorem eqProgram_out : forall a b dest st, out (programRun (eqProgram a b dest) st) = out st.
Proof.
  intros. unfold eqProgram, zeroPairProgram. cbn [programRun].
  rewrite loopRun_out by (intros; reflexivity).
  rewrite loopRun_out by (intros; reflexivity).
  change (out (programRun (subProgram b a (subCounter a b dest+3))
    (programRun (subProgram a b (subCounter a b dest)) st)) = out st).
  rewrite !subProgram_out. reflexivity.
Qed.
Theorem eqProgram_reaches : forall x k a b dest st,
  length (regs st) = k -> subCounter a b dest+5 < k ->
  exists c, Reaches (compileProgram k (eqProgram a b dest)) (encode 0 x st)
    (programCost x (eqProgram a b dest) st) c /\
    Similar (encode (length (program (compileProgram k (eqProgram a b dest)))) x
      (programRun (eqProgram a b dest) st)) c.
Proof. intros. apply compileProgram_reaches; [apply eqProgram_wellFormed; assumption|assumption]. Qed.

Definition branchProgram (flag alternative : nat) (yes no : Program) : Program :=
  sequence (sequence (clearRegister alternative) (straight (increment alternative 1)))
    (sequence (loop flag (sequence (clearRegister alternative) yes)) (loop alternative no)).
Definition ifLtProgram (a b flag alternative : nat) (yes no : Program) : Program :=
  sequence (ltProgram a b flag) (branchProgram flag alternative yes no).
Definition selectEqProgram (a b flag alternative : nat) (yes no : Program) : Program :=
  sequence (eqProgram a b flag) (branchProgram flag alternative yes no).

Theorem state_register_ext : forall st next,
  length (regs st) = length (regs next) -> out st = out next ->
  (forall i, registerAt i st = registerAt i next) -> st = next.
Proof.
  intros [rs w] [rs' w'] hl ho hv. cbn [regs out] in *. subst w'.
  assert (hr : rs = rs').
  { apply nth_ext with (d := 0) (d' := 0); [exact hl|]. intros i hi. exact (hv i). }
  subst rs'. reflexivity.
Qed.
Theorem putRegister_overwrite : forall slot value old st,
  putRegister slot value (putRegister slot old st) = putRegister slot value st.
Proof.
  intros slot value old [rs w]. unfold putRegister. cbn [regs out].
  f_equal. revert slot. induction rs; intros [|slot]; cbn [setRegister]; auto.
  rewrite IHrs. reflexivity.
Qed.
Theorem putRegister_commute : forall slot other value old st, slot <> other ->
  putRegister slot value (putRegister other old st) = putRegister other old (putRegister slot value st).
Proof.
  intros slot other value old [rs w] h. unfold putRegister. cbn [regs out].
  f_equal. revert slot other h. induction rs; intros [|slot] [|other] h; cbn [setRegister]; try reflexivity; try congruence.
  rewrite IHrs by lia. reflexivity.
Qed.
Theorem setFlag_state : forall dest st, dest < length (regs st) ->
  programRun (sequence (clearRegister dest) (straight (increment dest 1))) st = putRegister dest 1 st.
Proof.
  intros dest st hd. apply state_register_ext.
  - rewrite programRun_regs_length, putRegister_length. reflexivity.
  - reflexivity.
  - intros i. rewrite setFlag_registers by exact hd. destruct (i =? dest) eqn:he.
    + apply Nat.eqb_eq in he. subst i. symmetry. apply registerAt_putRegister; exact hd.
    + apply Nat.eqb_neq in he. symmetry. apply registerAt_putRegister_other; exact he.
Qed.
Theorem branchProgram_wellFormed : forall k flag alternative yes no,
  flag < k -> alternative < k -> flag <> alternative ->
  ProgramWellFormed k yes -> ProgramWellFormed k no ->
  ProgramReadOnly flag yes -> ProgramReadOnly alternative yes -> ProgramReadOnly alternative no ->
  ProgramWellFormed k (branchProgram flag alternative yes no).
Proof.
  intros. unfold branchProgram. cbn [ProgramWellFormed ProgramReadOnly WellFormed].
  repeat split; assumption.
Qed.
Theorem branchProgram_run : forall flag alternative yes no st,
  flag < length (regs st) -> alternative < length (regs st) -> flag <> alternative ->
  registerAt flag st <= 1 -> ProgramReadOnly alternative yes ->
  programRun (branchProgram flag alternative yes no) st =
    if registerAt flag st =? 0 then programRun no (putRegister alternative 0 st) else
    programRun yes (putRegister alternative 0 (putRegister flag 0 st)).
Proof.
  intros flag alternative yes no st hf ha hne hbit hya.
  unfold branchProgram. cbn [programRun].
  change (loopRun alternative (programRun no)
    (registerAt alternative (loopRun flag
      (programRun (sequence (clearRegister alternative) yes))
      (registerAt flag (programRun (sequence (clearRegister alternative) (straight (increment alternative 1))) st))
      (programRun (sequence (clearRegister alternative) (straight (increment alternative 1))) st)))
    (loopRun flag (programRun (sequence (clearRegister alternative) yes))
      (registerAt flag (programRun (sequence (clearRegister alternative) (straight (increment alternative 1))) st))
      (programRun (sequence (clearRegister alternative) (straight (increment alternative 1))) st)) =
    if registerAt flag st =? 0 then programRun no (putRegister alternative 0 st) else
    programRun yes (putRegister alternative 0 (putRegister flag 0 st))).
  rewrite setFlag_state by exact ha. rewrite registerAt_putRegister_other by exact hne.
  destruct (registerAt flag st =? 0) eqn:hz.
  - apply Nat.eqb_eq in hz. rewrite hz. cbn [loopRun].
    rewrite registerAt_putRegister by exact ha. cbn [loopRun].
    rewrite putRegister_overwrite. reflexivity.
  - apply Nat.eqb_neq in hz. assert (hone : registerAt flag st = 1) by lia.
    rewrite hone. cbn [loopRun programRun].
    rewrite (putRegister_commute flag alternative 0 1 st hne). rewrite putRegister_overwrite.
    rewrite programRun_readOnly by exact hya.
    rewrite registerAt_putRegister by (rewrite putRegister_length; exact ha).
    reflexivity.
Qed.
Theorem branchProgram_reaches : forall x k flag alternative yes no st,
  length (regs st) = k -> ProgramWellFormed k (branchProgram flag alternative yes no) ->
  exists c, Reaches (compileProgram k (branchProgram flag alternative yes no)) (encode 0 x st)
    (programCost x (branchProgram flag alternative yes no) st) c /\
    Similar (encode (length (program (compileProgram k (branchProgram flag alternative yes no)))) x
      (programRun (branchProgram flag alternative yes no) st)) c.
Proof. intros. apply compileProgram_reaches; assumption. Qed.
Theorem ifLtProgram_run : forall a b flag alternative yes no st,
  subCounter a b flag+2 < length (regs st) -> alternative < length (regs st) ->
  flag <> alternative -> ProgramReadOnly alternative yes ->
  programRun (ifLtProgram a b flag alternative yes no) st =
    let compared := programRun (ltProgram a b flag) st in
    if registerAt a st <? registerAt b st then
      programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
      programRun no (putRegister alternative 0 compared).
Proof.
  intros a b flag alternative yes no st hk ha hne hya.
  set (compared := programRun (ltProgram a b flag) st).
  destruct (subCounter_wider a b flag) as [h1 [h2 h3]].
  assert (hl : length (regs compared) = length (regs st)) by apply programRun_regs_length.
  assert (hf : registerAt flag compared = if registerAt a st <? registerAt b st then 1 else 0).
  { unfold compared. rewrite ltProgram_registers by exact hk.
    assert (hno : (subCounter a b flag <=? flag) = false) by (apply Nat.leb_gt; exact h3).
    rewrite hno, Nat.eqb_refl. reflexivity. }
  assert (hbit : registerAt flag compared <= 1) by (rewrite hf; destruct (registerAt a st <? registerAt b st); lia).
  change (programRun (branchProgram flag alternative yes no) compared =
    if registerAt a st <? registerAt b st then
      programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
      programRun no (putRegister alternative 0 compared)).
  rewrite branchProgram_run by (try lia; assumption). rewrite hf.
  destruct (registerAt a st <? registerAt b st); reflexivity.
Qed.
Theorem selectEqProgram_run : forall a b flag alternative yes no st,
  subCounter a b flag+5 < length (regs st) -> alternative < length (regs st) ->
  flag <> alternative -> ProgramReadOnly alternative yes ->
  programRun (selectEqProgram a b flag alternative yes no) st =
    let compared := programRun (eqProgram a b flag) st in
    if registerAt a st =? registerAt b st then
      programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
      programRun no (putRegister alternative 0 compared).
Proof.
  intros a b flag alternative yes no st hk ha hne hya.
  set (compared := programRun (eqProgram a b flag) st).
  destruct (subCounter_wider a b flag) as [h1 [h2 h3]].
  assert (hl : length (regs compared) = length (regs st)) by apply programRun_regs_length.
  assert (hf : registerAt flag compared = if registerAt a st =? registerAt b st then 1 else 0).
  { unfold compared. rewrite eqProgram_registers by exact hk.
    assert (hno : (subCounter a b flag <=? flag) = false) by (apply Nat.leb_gt; exact h3).
    rewrite hno, Nat.eqb_refl. reflexivity. }
  assert (hbit : registerAt flag compared <= 1) by (rewrite hf; destruct (registerAt a st =? registerAt b st); lia).
  change (programRun (branchProgram flag alternative yes no) compared =
    if registerAt a st =? registerAt b st then
      programRun yes (putRegister alternative 0 (putRegister flag 0 compared)) else
      programRun no (putRegister alternative 0 compared)).
  rewrite branchProgram_run by (try lia; assumption). rewrite hf.
  destruct (registerAt a st =? registerAt b st); reflexivity.
Qed.
Theorem ifLtProgram_wellFormed : forall k a b flag alternative yes no,
  subCounter a b flag+2 < k -> ProgramWellFormed k (branchProgram flag alternative yes no) ->
  ProgramWellFormed k (ifLtProgram a b flag alternative yes no).
Proof. intros. split; [apply ltProgram_wellFormed|]; assumption. Qed.
Theorem selectEqProgram_wellFormed : forall k a b flag alternative yes no,
  subCounter a b flag+5 < k -> ProgramWellFormed k (branchProgram flag alternative yes no) ->
  ProgramWellFormed k (selectEqProgram a b flag alternative yes no).
Proof. intros. split; [apply eqProgram_wellFormed|]; assumption. Qed.

End Arithmetic.
