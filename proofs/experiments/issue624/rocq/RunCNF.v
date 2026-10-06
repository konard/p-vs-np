From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue568.rocq Require Import Tableau.
From proofs.experiments.issue624.rocq Require Import LocalCNF MachineCNF FixedWindow SuccessorCNF.
Import ListNotations.

(** Bounded accepting prefixes of finite rows, using the existing localTrace.
    Stop bits distinguish an accepting halt from a charged successor move.
    Suffixes after a halt are unconstrained. Initial wiring is still separate. *)
Module RunCNF.
Import Complexity Machines Tableau LocalCNF MachineCNF SuccessorCNF.

Definition guarded (l : Lit) (f : CNF) : CNF := map (implies [l]) f.

Theorem guarded_models : forall a l f,
  evalCNF a (guarded l f) = true <-> (evalLit a l = true -> evalCNF a f = true).
Proof.
  intros a l f. unfold guarded. induction f as [|c f IH].
  - simpl. intuition.
  - cbn [map evalCNF]. rewrite !andb_true_iff, implies_models, IH.
    split.
    + intros [hc hf] hl. split; [apply hc; intros x [he|he]; [subst; exact hl|contradiction]|auto].
    + intros hf. split.
      * intro hc. apply (proj1 (hf (hc l (or_introl eq_refl)))).
      * intro hl. apply (proj2 (hf hl)).
Qed.

Definition haltRule (m : Machine) (base width q h s : nat) : CNF :=
  match instruction m q (symbolOfIndex s) with
  | halt true => []
  | _ => [implies (guard base (length (program m)) width q h s) []]
  end.
Definition haltCNF (m : Machine) (base width : nat) : CNF :=
  flat_map (fun q => flat_map (fun h => flat_map
    (fun s => haltRule m base width q h s) (seq 0 4)) (seq 0 width)) (seq 0 (length (program m))).

Theorem haltRule_models : forall m base width q h s a,
  evalCNF a (haltRule m base width q h s) = true <->
    ((forall l, In l (guard base (length (program m)) width q h s) -> evalLit a l = true) ->
      instruction m q (symbolOfIndex s) = halt true).
Proof.
  intros. unfold haltRule. destruct (instruction m q (symbolOfIndex s)) as [[]|target write dir];
    cbn [evalCNF]; try (split; intros; reflexivity).
  all: rewrite andb_true_r, implies_models; simpl evalClause; split.
  all: try (intros hf hp; specialize (hf hp); discriminate).
  all: intros hf hp; specialize (hf hp); discriminate.
Qed.

Theorem haltCNF_step : forall m base width a c,
  RowRepresents a base (length (program m)) width c ->
  (evalCNF a (haltCNF m base width) = true <-> step m c = inl true).
Proof.
  intros m base width a c hc.
  assert (hs : step m c = inl true <-> instruction m (state c) (tapeHead c) = halt true).
  { unfold step. destruct (instruction m (state c) (tapeHead c)) as [b|q w d]; split;
      intro h; inversion h; reflexivity. }
  rewrite hs. unfold haltCNF. rewrite evalCNF_flatMap. split.
  - intro hf. pose proof (proj1 (proj1 (proj2 hc))) as hq.
    pose proof (proj1 (proj1 (proj2 (proj2 hc)))) as hh.
    specialize (hf (state c) ltac:(apply in_seq; lia)). rewrite evalCNF_flatMap in hf.
    specialize (hf (length (tapeLeft c)) ltac:(apply in_seq; lia)). rewrite evalCNF_flatMap in hf.
    specialize (hf (symbolIndex (tapeHead c)) ltac:(apply in_seq; pose proof (symbolIndex_lt (tapeHead c)); lia)).
    apply haltRule_models in hf. rewrite <- (symbolOfIndex_index (tapeHead c)). apply hf.
    apply (proj2 (guard_models a _ _ _ c hc _ _ _ hq hh (symbolIndex_lt (tapeHead c)))).
    repeat split; auto. apply symbolOfIndex_index.
  - intros hf q hq. apply in_seq in hq. rewrite evalCNF_flatMap.
    intros h hh. apply in_seq in hh. rewrite evalCNF_flatMap.
    intros s hs'. apply in_seq in hs'. apply haltRule_models.
    intro hg. destruct (proj1 (guard_models a _ _ _ c hc q h s ltac:(lia) ltac:(lia) ltac:(lia)) hg)
      as [heq [heh hes]]. subst q h. rewrite hes. exact hf.
Qed.

Definition stride states width := states + 5 * width + 1.
Definition stopVar base states width := base + states + 5 * width.
Definition nextBase base states width := base + stride states width.

Fixpoint runCNF (m : Machine) (base width fuel : nat) : CNF :=
  match fuel with
  | 0 => [[]]
  | S k =>
    let stop := stopVar base (length (program m)) width in
    let next := nextBase base (length (program m)) width in
    (rowCNF base (length (program m)) width ++ guarded (mkLit stop true) (haltCNF m base width)) ++
      guarded (mkLit stop false) (successorCNF m base next width ++ runCNF m next width k)
  end.

Definition isEmpty {A : Type} (xs : list A) : bool := match xs with [] => true | _ => false end.
Fixpoint TraceRepresents (a : Assignment) (base states width : nat) (trace : list Config) : Prop :=
  match trace with
  | [] => False
  | c :: rest => RowRepresents a base states width c /\
    a (stopVar base states width) = isEmpty rest /\
    (rest <> [] -> TraceRepresents a (nextBase base states width) states width rest)
  end.
Fixpoint decodeTrace (m : Machine) (base width fuel : nat) (a : Assignment) : list Config :=
  match fuel with
  | 0 => []
  | S k => decodeRow a base (length (program m)) width ::
    if a (stopVar base (length (program m)) width) then []
    else decodeTrace m (nextBase base (length (program m)) width) width k a
  end.

Theorem runCNF_unfold : forall m base width k a,
  evalCNF a (runCNF m base width (S k)) = true <->
    evalCNF a (rowCNF base (length (program m)) width) = true /\
    (a (stopVar base (length (program m)) width) = true -> evalCNF a (haltCNF m base width) = true) /\
    (a (stopVar base (length (program m)) width) = false ->
      evalCNF a (successorCNF m base (nextBase base (length (program m)) width) width) = true /\
      evalCNF a (runCNF m (nextBase base (length (program m)) width) width k) = true).
Proof.
  intros. cbn [runCNF]. rewrite !evalCNF_append, !andb_true_iff, !guarded_models.
  rewrite evalCNF_append, andb_true_iff.
  unfold evalLit. cbn [pos var].
  destruct (a (stopVar base (length (program m)) width)); cbn [Bool.eqb]; intuition congruence.
Qed.

Theorem decodeTrace_length : forall m base width fuel a, length (decodeTrace m base width fuel a) <= fuel.
Proof.
  intros m base width fuel. revert base. induction fuel; intros base a; cbn [decodeTrace length]; [lia|].
  destruct (a (stopVar base (length (program m)) width)); cbn [length]; [lia|].
  specialize (IHfuel (nextBase base (length (program m)) width) a). lia.
Qed.

Theorem runCNF_sound : forall m base width fuel a,
  evalCNF a (runCNF m base width fuel) = true ->
    TraceRepresents a base (length (program m)) width (decodeTrace m base width fuel a) /\
      localTrace m true (decodeTrace m base width fuel a).
Proof.
  intros m base width fuel. revert base. induction fuel as [|k IH]; intros base a hf;
    [discriminate|].
  apply runCNF_unfold in hf. destruct hf as [hr [ht hn]].
  apply rowCNF_models in hr. cbn [decodeTrace].
  destruct (a (stopVar base (length (program m)) width)) eqn:he.
  - split.
    + cbn [TraceRepresents isEmpty]. split; [exact hr|]. split; [exact he|].
      intros hc. exfalso. apply hc. reflexivity.
    + apply (proj1 (haltCNF_step m base width a _ hr)). apply ht. reflexivity.
  - destruct (hn eq_refl) as [hs hf]. specialize (IH _ a hf).
    destruct IH as [hrep hlocal].
    destruct (decodeTrace m (nextBase base (length (program m)) width) width k a) as [|d tail] eqn:hd;
      [contradiction|].
    pose proof (proj2 (proj2 (proj1 (successorCNF_models m base
      (nextBase base (length (program m)) width) width a) hs))) as hstep.
    rewrite (decodeRow_represents a _ _ _ d (proj1 hrep)) in hstep.
    split.
    + cbn [TraceRepresents isEmpty]. split; [exact hr|]. split; [exact he|]. auto.
    + change (step m (decodeRow a base (length (program m)) width) = inr d /\ localTrace m true (d :: tail)).
      auto.
Qed.

Theorem runCNF_complete : forall m base width fuel a trace,
  TraceRepresents a base (length (program m)) width trace -> localTrace m true trace ->
  length trace <= fuel -> evalCNF a (runCNF m base width fuel) = true.
Proof.
  intros m base width fuel. revert base. induction fuel as [|k IH]; intros base a trace hr hl hb.
  - destruct trace; [contradiction|cbn [length] in hb |- *; lia].
  - destruct trace as [|c rest]; [contradiction|]. destruct hr as [hc [he ht]].
    apply runCNF_unfold. split; [apply rowRepresents_models with c; exact hc|]. split.
    + intro hstop. destruct rest as [|d tail]; [apply (proj2 (haltCNF_step m base width a c hc)); exact hl|].
      simpl isEmpty in he. congruence.
    + intro hgo. destruct rest as [|d tail]; [simpl isEmpty in he; congruence|].
      specialize (ht ltac:(discriminate)). split.
      * apply (proj2 (successorCNF_step m base _ width a c d hc (proj1 ht))). exact (proj1 hl).
      * apply IH with (trace := d :: tail); [exact ht|exact (proj2 hl)|cbn [length] in hb |- *; lia].
Qed.

Theorem runCNF_models : forall m base width fuel a,
  evalCNF a (runCNF m base width fuel) = true <->
    exists trace, TraceRepresents a base (length (program m)) width trace /\
      length trace <= fuel /\ localTrace m true trace.
Proof.
  intros. split.
  - intro hf. destruct (runCNF_sound m base width fuel a hf) as [hr hl].
    exists (decodeTrace m base width fuel a). repeat split; auto using decodeTrace_length.
  - intros [trace [hr [hb hl]]]. eapply runCNF_complete; eauto.
Qed.

Theorem runCNF_wrong_successor_rejected : forall m base width fuel a c d rest,
  step m c <> inr d -> decodeTrace m base width fuel a = c :: d :: rest ->
    evalCNF a (runCNF m base width fuel) = false.
Proof.
  intros m base width fuel a c d rest hs hd.
  destruct (evalCNF a (runCNF m base width fuel)) eqn:hf; [|reflexivity].
  destruct (runCNF_sound m base width fuel a hf) as [_ hl]. rewrite hd in hl.
  contradiction (hs (proj1 hl)).
Qed.

Fixpoint traceAssignment (base states width : nat) (trace : list Config) : Assignment :=
  match trace with
  | [] => fun _ => false
  | c :: rest => fun v =>
    if v <? stopVar base states width then rowAssignment base states width c v
    else if v =? stopVar base states width then isEmpty rest
    else traceAssignment (nextBase base states width) states width rest v
  end.

Theorem rowRepresents_congr : forall a b base states width c,
  (forall v, base <= v -> v < stopVar base states width -> a v = b v) ->
    RowRepresents a base states width c -> RowRepresents b base states width c.
Proof.
  intros a b base states width c he hc.
  assert (hs : forall offset size value, base <= offset -> offset + size <= stopVar base states width ->
    Selected a offset size value -> Selected b offset size value).
  { intros offset size value hb hu [hv [ho hon]]. split; [exact hv|]. split.
    - rewrite <- he by lia. exact ho.
    - intros j hj hj'. apply hon; [exact hj|]. rewrite he by lia. exact hj'. }
  destruct hc as [hw [hq [hh ht]]]. split; [exact hw|]. split.
  - apply hs; [lia|unfold stopVar; lia|exact hq].
  - split.
    + apply hs; [lia|unfold stopVar; lia|exact hh].
    + intros i hi. apply hs; [unfold tapeBase; lia|unfold tapeBase, stopVar; lia|apply ht; exact hi].
Qed.

Theorem traceRepresents_congr : forall a b base states width trace,
  (forall v, base <= v -> a v = b v) -> TraceRepresents a base states width trace ->
    TraceRepresents b base states width trace.
Proof.
  intros a b base states width trace. revert base. induction trace as [|c rest IH]; intros base he hr;
    [contradiction|]. destruct hr as [hc [hs ht]]. cbn [TraceRepresents]. split.
  - eapply rowRepresents_congr; [intros; apply he; assumption|exact hc].
  - split.
    + rewrite <- he by (unfold stopVar; lia). exact hs.
    + intro hn. apply IH; [intros v hv; apply he; unfold nextBase, stride in hv; lia|auto].
Qed.

Theorem traceAssignment_represents : forall base states width trace,
  trace <> [] -> (forall c, In c trace -> span c = width /\ state c < states) ->
    TraceRepresents (traceAssignment base states width trace) base states width trace.
Proof.
  intros base states width trace. revert base. induction trace as [|c rest IH]; intros base hn hc;
    [contradiction hn; reflexivity|].
  pose proof (hc c (or_introl eq_refl)) as [hw hq]. cbn [TraceRepresents]. split.
  - eapply rowRepresents_congr; [|apply rowAssignment_represents; assumption].
    intros v hb hv. cbn [traceAssignment]. rewrite (proj2 (Nat.ltb_lt _ _) hv). reflexivity.
  - split.
    + cbn [traceAssignment]. rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity.
    + intro ht. eapply traceRepresents_congr.
      * intros v hv. cbn [traceAssignment].
        assert (h0 : (v <? stopVar base states width) = false) by
          (apply Nat.ltb_ge; unfold nextBase, stride, stopVar in *; lia).
        assert (h1 : (v =? stopVar base states width) = false) by
          (apply Nat.eqb_neq; unfold nextBase, stride, stopVar in *; lia).
        rewrite h0, h1. reflexivity.
      * apply IH; [exact ht|intros d hd; apply hc; right; exact hd].
Qed.

Theorem decodeTrace_represents : forall m base width fuel a trace,
  TraceRepresents a base (length (program m)) width trace -> length trace <= fuel ->
    decodeTrace m base width fuel a = trace.
Proof.
  intros m base width fuel. revert base. induction fuel as [|k IH]; intros base a trace hr hb.
  - destruct trace; [contradiction|cbn [length] in hb |- *; lia].
  - destruct trace as [|c rest]; [contradiction|]. destruct hr as [hc [he ht]].
    cbn [decodeTrace]. rewrite (decodeRow_represents a _ _ _ c hc), he.
    destruct rest as [|d tail]; [reflexivity|]. simpl isEmpty. f_equal.
    apply IH; [apply ht; discriminate|cbn [length] in hb |- *; lia].
Qed.

Theorem runCNF_traceAssignment : forall m base width fuel trace,
  localTrace m true trace -> length trace <= fuel -> (forall c, In c trace -> span c = width) ->
    evalCNF (traceAssignment base (length (program m)) width trace) (runCNF m base width fuel) = true /\
    decodeTrace m base width fuel (traceAssignment base (length (program m)) width trace) = trace.
Proof.
  intros m base width fuel trace hl hb hw.
  assert (hne : trace <> []) by (intro he; subst; contradiction).
  assert (hr : TraceRepresents (traceAssignment base (length (program m)) width trace)
    base (length (program m)) width trace).
  { apply traceAssignment_represents; [exact hne|]. intros c hc. split; [apply hw; exact hc|].
    apply (FixedWindow.accepting_trace_state_lt m trace hl c hc). }
  split; [eapply runCNF_complete; eauto|apply decodeTrace_represents; auto].
Qed.

Theorem traceRepresents_width : forall a base states width trace,
  TraceRepresents a base states width trace -> forall c, In c trace -> span c = width.
Proof.
  intros a base states width trace. revert base. induction trace as [|d rest IH]; intros base hr c hc;
    [contradiction|]. destruct hc as [he|hc]; [subst; exact (proj1 (proj1 hr))|].
  eapply IH; [apply (proj2 (proj2 hr)); intro he; subst; contradiction|exact hc].
Qed.

Theorem runCNF_iff : forall m base width fuel,
  Satisfiable (runCNF m base width fuel) <->
    exists trace, length trace <= fuel /\ localTrace m true trace /\ forall c, In c trace -> span c = width.
Proof.
  intros. split.
  - intros [a hf]. apply runCNF_models in hf. destruct hf as [trace [hr [hb hl]]].
    exists trace. split; [exact hb|]. split; [exact hl|]. eapply traceRepresents_width; exact hr.
  - intros [trace [hb [hl hw]]]. exists (traceAssignment base (length (program m)) width trace).
    apply (proj1 (runCNF_traceAssignment m base width fuel trace hl hb hw)).
Qed.

Theorem runCNF_rejecting_unsatisfiable : forall m base width fuel,
  (forall c, step m c = inl false) -> ~ Satisfiable (runCNF m base width fuel).
Proof.
  intros m base width fuel hm hf. apply runCNF_iff in hf. destruct hf as [trace [_ [hl _]]].
  destruct trace as [|c rest]; [contradiction|]. destruct rest as [|d tail]; cbn [localTrace] in hl.
  - rewrite (hm c) in hl. discriminate.
  - destruct hl as [hs _]. rewrite (hm c) in hs. discriminate.
Qed.

Theorem haltCNF_length : forall m base width, length (haltCNF m base width) <= 4 * length (program m) * width.
Proof.
  intros. assert (hi : forall q h, length (flat_map (fun s => haltRule m base width q h s) (seq 0 4)) <= 4).
  { intros. replace 4 with (length (seq 0 4) * 1) at 2 by reflexivity. apply flatMap_length_le.
    intros s _. unfold haltRule. destruct (instruction m q (symbolOfIndex s)) as [[]|target write dir]; simpl; lia. }
  assert (hh : forall q, length (flat_map (fun h => flat_map
    (fun s => haltRule m base width q h s) (seq 0 4)) (seq 0 width)) <= width * 4).
  { intros. rewrite <- (length_seq width 0) at 2. apply flatMap_length_le. intros. apply hi. }
  unfold haltCNF. replace (4 * length (program m) * width)
    with (length (seq 0 (length (program m))) * (width * 4)) by (rewrite length_seq; nia).
  apply flatMap_length_le. intros. apply hh.
Qed.

Theorem haltCNF_bounds : forall m base width,
  VarsBelow (stopVar base (length (program m)) width) (haltCNF m base width) /\
    forall c, In c (haltCNF m base width) -> length c <= 3.
Proof.
  intros m base width.
  assert (hb : forall c, In c (haltCNF m base width) ->
    (forall l, In l c -> var l < stopVar base (length (program m)) width) /\ length c <= 3).
  { intros c hc. unfold haltCNF in hc. apply in_flat_map in hc. destruct hc as [q [hq hc]].
    apply in_flat_map in hc. destruct hc as [h [hh hc]].
    apply in_flat_map in hc. destruct hc as [s [hs hc]].
    apply in_seq in hq. apply in_seq in hh. apply in_seq in hs.
    unfold haltRule in hc. destruct (instruction m q (symbolOfIndex s)) as [[]|target write dir];
      try contradiction; destruct hc as [he|he]; try contradiction; subst c;
      unfold implies, guard, negate; simpl; split; [|lia| |lia].
    all: intros l [he|[he|[he|he]]]; try contradiction; subst l;
      unfold stateVar, headVar, tapeVar, tapeBase, stopVar; simpl; lia. }
  split; [intros c hc; exact (proj1 (hb c hc))|intros c hc; exact (proj2 (hb c hc))].
Qed.

Definition runCount (m : Machine) width := length (program m) * length (program m) +
  width * width + 17 * width + 2 + 4 * length (program m) * width + successorCount m width.

Theorem runCNF_length : forall m base width fuel,
  length (runCNF m base width fuel) <= fuel * runCount m width + 1.
Proof.
  intros m base width fuel. revert base. induction fuel as [|k IH]; intro base; [simpl; lia|].
  pose proof (rowCNF_length base (length (program m)) width).
  pose proof (haltCNF_length m base width).
  pose proof (successorCNF_length m base (nextBase base (length (program m)) width) width).
  specialize (IH (nextBase base (length (program m)) width)).
  cbn [runCNF]. unfold guarded. rewrite !length_app, !length_map, !length_app.
  unfold runCount in *. nia.
Qed.

Theorem guarded_bounds : forall l f bound width,
  var l < bound -> VarsBelow bound f -> (forall c, In c f -> length c <= width) ->
    VarsBelow bound (guarded l f) /\ forall c, In c (guarded l f) -> length c <= width + 1.
Proof.
  intros l f bound width hl hv hw. unfold guarded. split.
  - intros c hc t ht. apply in_map_iff in hc. destruct hc as [d [he hd]]. subst c.
    unfold implies in ht. simpl in ht. destruct ht as [he|ht]; [subst; exact hl|apply (hv d hd t ht)].
  - intros c hc. apply in_map_iff in hc. destruct hc as [d [he hd]]. subst c.
    unfold implies. simpl. pose proof (hw d hd). lia.
Qed.

Theorem runCNF_bounds : forall m base width fuel,
  VarsBelow (base + (fuel + 1) * stride (length (program m)) width) (runCNF m base width fuel) /\
    forall c, In c (runCNF m base width fuel) -> length c <= length (program m) + width + 6 + fuel.
Proof.
  intros m base width fuel. revert base. induction fuel as [|k IH]; intro base.
  - split; [intros c [he|he] l hl; [subst; contradiction|contradiction]|].
    intros c [he|he]; [subst; simpl; lia|contradiction].
  - set (next := nextBase base (length (program m)) width).
    set (bound := base + (S k + 1) * stride (length (program m)) width).
    set (cw := length (program m) + width + 6 + k).
    destruct (IH next) as [hnv hnw].
    destruct (rowCNF_bounds base (length (program m)) width) as [hrv hrw].
    destruct (haltCNF_bounds m base width) as [hhv hhw].
    destruct (successorCNF_bounds m base next width) as [hsv hsw].
    assert (hb : stopVar base (length (program m)) width < bound).
    { unfold stopVar, bound, stride. nia. }
    assert (he : next + (k + 1) * stride (length (program m)) width = bound).
    { unfold next, nextBase, bound. nia. }
    assert (hmax : Nat.max base next = next) by (apply Nat.max_r; unfold next, nextBase; lia).
    assert (hsvb : next + length (program m) + 5 * width <= bound).
    { unfold next, nextBase, bound, stride. nia. }
    destruct (guarded_bounds (mkLit (stopVar base (length (program m)) width) true)
      (haltCNF m base width) bound cw hb
      ltac:(intros c hc l hl; pose proof (hhv c hc l hl); lia)
      ltac:(intros c hc; pose proof (hhw c hc); unfold cw; lia)) as [hhaltv hhaltw].
    destruct (guarded_bounds (mkLit (stopVar base (length (program m)) width) false)
      (successorCNF m base next width ++ runCNF m next width k) bound cw hb
      ltac:(intros c hc l hl; apply in_app_or in hc; destruct hc as [hc|hc];
        [pose proof (hsv c hc l hl); rewrite hmax in H; lia|rewrite <- he; apply (hnv c hc l hl)])
      ltac:(intros c hc; apply in_app_or in hc; destruct hc as [hc|hc];
        [pose proof (hsw c hc); unfold cw; lia|apply (hnw c hc)])) as [hgov hgow].
    cbn [runCNF]. fold next. split.
    + intros c hc l hl. apply in_app_or in hc. destruct hc as [hc|hc]; [|apply (hgov c hc l hl)].
      apply in_app_or in hc. destruct hc as [hc|hc]; [|apply (hhaltv c hc l hl)].
      pose proof (hrv c hc l hl). unfold bound, stride. nia.
    + intros c hc. apply in_app_or in hc. destruct hc as [hc|hc];
        [|pose proof (hgow c hc); unfold cw in *; lia].
      apply in_app_or in hc. destruct hc as [hc|hc];
        [pose proof (hrw c hc); lia|pose proof (hhaltw c hc); unfold cw in *; lia].
Qed.

Definition runSize (m : Machine) base width fuel := 2 * (fuel * runCount m width + 1) *
  (1 + (length (program m) + width + 6 + fuel) *
    (base + (fuel + 1) * stride (length (program m)) width + 1)).

Theorem runCNF_encoded_size : forall m base width fuel,
  length (encodeCNF (runCNF m base width fuel)) <= runSize m base width fuel.
Proof.
  intros. destruct (runCNF_bounds m base width fuel) as [hv hw].
  pose proof (cnf_encoded_size _ _ _ hv hw) as hs.
  pose proof (runCNF_length m base width fuel) as hc. unfold runSize. nia.
Qed.

(** An explicit envelope for polynomial offset, window, and clock bounds. *)
Definition runPolynomial (m : Machine) (b w t : Polynomial) : Polynomial :=
  let c := fun n => {| coefficient := n; degree := 0 |} in
  let q := c (length (program m)) in
  let row := polyAdd (polyAdd (polyAdd (polyMul q q) (polyMul w w)) (polyMul (c 17) w)) (c 2) in
  let moves := polyMul (polyMul (polyMul (c 4) q) w) (polyAdd (polyMul (c 4) w) (c 2)) in
  let count := polyAdd (polyAdd row (polyMul (polyMul (c 4) q) w))
    (polyAdd (polyMul (c 2) row) moves) in
  let stepWidth := polyAdd (polyAdd (polyAdd q w) (c 6)) t in
  let stepStride := polyAdd (polyAdd q (polyMul (c 5) w)) (c 1) in
  let variables := polyAdd (polyAdd b (polyMul (polyAdd t (c 1)) stepStride)) (c 1) in
  polyMul (polyMul (c 2) (polyAdd (polyMul t count) (c 1)))
    (polyAdd (c 1) (polyMul stepWidth variables)).

Theorem runCNF_polynomial_size : forall m b w t n base width fuel,
  base <= evalPoly b n -> width <= evalPoly w n -> fuel <= evalPoly t n ->
  length (encodeCNF (runCNF m base width fuel)) <= evalPoly (runPolynomial m b w t) n.
Proof.
  intros m b w t n base width fuel hb hw ht.
  assert (add : forall p q u v, u <= evalPoly p n -> v <= evalPoly q n ->
    u + v <= evalPoly (polyAdd p q) n).
  { intros. eapply Nat.le_trans; [apply Nat.add_le_mono; eassumption|apply polyAdd_eval]. }
  assert (mul : forall p q u v, u <= evalPoly p n -> v <= evalPoly q n ->
    u * v <= evalPoly (polyMul p q) n).
  { intros. rewrite <- polyMul_eval. apply Nat.mul_le_mono; assumption. }
  assert (const : forall k, k <= evalPoly {| coefficient := k; degree := 0 |} n).
  { intros. unfold evalPoly. simpl. lia. }
  pose proof (add _ _ _ _ (add _ _ _ _
    (add _ _ _ _ (mul _ _ _ _ (const (length (program m))) (const (length (program m))))
      (mul _ _ _ _ hw hw)) (mul _ _ _ _ (const 17) hw)) (const 2)) as hrow.
  pose proof (mul _ _ _ _ (mul _ _ _ _ (const 4) (const (length (program m)))) hw) as hprod.
  pose proof (add _ _ _ _ (add _ _ _ _ hrow hprod)
    (add _ _ _ _ (mul _ _ _ _ (const 2) hrow)
      (mul _ _ _ _ hprod (add _ _ _ _ (mul _ _ _ _ (const 4) hw) (const 2))))) as hcount.
  pose proof (add _ _ _ _ (add _ _ _ _ (add _ _ _ _ (const (length (program m))) hw) (const 6)) ht) as hwidth.
  pose proof (add _ _ _ _ (add _ _ _ _ (const (length (program m)))
    (mul _ _ _ _ (const 5) hw)) (const 1)) as hstride.
  pose proof (add _ _ _ _ (add _ _ _ _ hb
    (mul _ _ _ _ (add _ _ _ _ ht (const 1)) hstride)) (const 1)) as hvars.
  pose proof (mul _ _ _ _ (mul _ _ _ _ (const 2)
    (add _ _ _ _ (mul _ _ _ _ ht hcount) (const 1)))
    (add _ _ _ _ (const 1) (mul _ _ _ _ hwidth hvars))) as hsize.
  exact (Nat.le_trans _ _ _ (runCNF_encoded_size m base width fuel) hsize).
Qed.

End RunCNF.
