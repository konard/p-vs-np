From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
Import ListNotations.

(** The first Cook--Levin slice over the shared finite machine. A trace lists
    configurations before each charged instruction. CNF encoding is later. *)
Module Tableau.
Import Complexity.

Fixpoint localTrace (m : Machine) (b : bool) (trace : list Config) : Prop :=
  match trace with
  | [] => False
  | c :: rest =>
      match rest with
      | [] => step m c = inl b
      | d :: _ => step m c = inr d /\ localTrace m b rest
      end
  end.

Definition boundedTableau (m : Machine) (c : Config) (clock : nat)
    (b : bool) : Prop :=
  exists trace : list Config,
    hd_error trace = Some c /\ length trace <= clock /\ localTrace m b trace.

(** Number of explicitly represented tape cells, including the head. *)
Definition span (c : Config) : nat :=
  length (tapeLeft c) + 1 + length (tapeRight c).

Lemma moveHead_span_le : forall c q w dir,
  span (moveHead c q w dir) <= span c + 1.
Proof.
  intros [s l h r] q w dir.
  destruct dir; destruct l; destruct r; unfold span; simpl; lia.
Qed.

Lemma step_span_le : forall m c d,
  step m c = inr d -> span d <= span c + 1.
Proof.
  intros m c d hs. unfold step in hs.
  destruct (instruction m (state c) (tapeHead c)) as [b|q w dir];
    [discriminate|].
  inversion hs. subst d. apply moveHead_span_le.
Qed.

(** Every represented configuration fits a tape window growing by at most
    one cell per charged instruction. *)
Theorem trace_span_bound : forall m b trace c d,
  hd_error trace = Some c -> localTrace m b trace -> In d trace ->
  span d <= span c + length trace.
Proof.
  intros m b trace. induction trace as [|first rest IH];
    intros c d hhead hlocal hin.
  - discriminate.
  - destruct rest as [|next tail].
    + simpl in hhead. inversion hhead. subst c.
      simpl in hin. destruct hin as [heq|[]]. subst d. simpl. lia.
    + simpl in hhead. inversion hhead. subst c.
      simpl in hlocal. destruct hlocal as [hs ht].
      simpl in hin. destruct hin as [heq|hin].
      * subst d. simpl. lia.
      * pose proof (IH next d eq_refl ht hin) as hrest.
        pose proof (step_span_le m first next hs) as hstep.
        simpl in hrest |- *. lia.
Qed.

Theorem initial_span_le : forall x : Word,
  span (initial x) <= length x + 1.
Proof.
  intros [|bit rest]; unfold span, initial, initialSymbols; simpl.
  - lia.
  - rewrite length_map. lia.
Qed.

(** A cell bound, not yet an encoded CNF bit-size bound. *)
Theorem bounded_initial_span : forall m x clock b trace d,
  hd_error trace = Some (initial x) ->
  length trace <= clock -> localTrace m b trace -> In d trace ->
  span d <= length x + clock + 1.
Proof.
  intros m x clock b trace d hstart hclock hlocal hin.
  pose proof (trace_span_bound m b trace (initial x) d hstart hlocal hin) as hspan.
  pose proof (initial_span_le x) as hinit. lia.
Qed.

Lemma trace_sound : forall m b trace, localTrace m b trace ->
  exists c, hd_error trace = Some c /\ Run m c (length trace) b.
Proof.
  intros m b trace. induction trace as [|c rest IH].
  - simpl. contradiction.
  - destruct rest as [|d tail].
    + simpl. intro h. exists c. split; [reflexivity|].
      apply run_halt. exact h.
    + simpl. intros [hs ht].
      destruct (IH ht) as [c' [hc' hr]].
      simpl in hc'. inversion hc'. subst c'.
      exists c. split; [reflexivity|].
      apply run_next with (c' := d); assumption.
Qed.

Lemma trace_complete : forall m c t b, Run m c t b ->
  exists trace : list Config,
    hd_error trace = Some c /\ length trace = t /\ localTrace m b trace.
Proof.
  intros m c t b hr. induction hr as [c b hs|c d t b hs hr IH].
  - exists [c]. simpl. auto.
  - destruct IH as [trace [hhead [hlen hlocal]]].
    destruct trace as [|first rest]; [discriminate|].
    simpl in hhead. inversion hhead. subst first.
    exists (c :: d :: rest). simpl. repeat split; auto.
Qed.

Theorem localTrace_iff_run : forall m c t b,
  (exists trace : list Config,
    hd_error trace = Some c /\ length trace = t /\ localTrace m b trace) <->
  Run m c t b.
Proof.
  intros m c t b. split.
  - intros [trace [hhead [hlen hlocal]]].
    destruct (trace_sound m b trace hlocal) as [c' [hc' hr]].
    rewrite hhead in hc'. inversion hc'. subst c'.
    now rewrite hlen in hr.
  - apply trace_complete.
Qed.

Theorem boundedAccept_iff_run : forall m c clock,
  boundedTableau m c clock true <->
  exists t, t <= clock /\ Run m c t true.
Proof.
  intros m c clock. split.
  - intros [trace [hhead [hbound hlocal]]].
    exists (length trace). split; [exact hbound|].
    apply (proj1 (localTrace_iff_run m c (length trace) true)).
    exists trace. auto.
  - intros [t [hbound hr]].
    destruct (proj2 (localTrace_iff_run m c t true) hr)
      as [trace [hhead [hlen hlocal]]].
    exists trace. repeat split; auto. now rewrite hlen.
Qed.

(** Degenerate and malformed tableaux have semantic counterexamples. *)
Definition acceptMachine : Machine :=
  {| program := [[halt true]] |}.
Definition loopMachine : Machine :=
  {| program := [[move 0 blank right]] |}.
Definition moveThenAccept : Machine :=
  {| program := [[move 1 blank stay];
                 [halt true; halt true; halt true; halt true]] |}.
Definition goodSuccessor : Config :=
  {| state := 1; tapeLeft := []; tapeHead := blank; tapeRight := [] |}.
Definition wrongSuccessor : Config :=
  {| state := 1; tapeLeft := []; tapeHead := one; tapeRight := [] |}.

Theorem empty_rejected : forall m b, ~ localTrace m b [].
Proof. intros m b h. exact h. Qed.

Theorem singleton_accepts : localTrace acceptMachine true [initial []].
Proof. reflexivity. Qed.

Theorem wrong_answer_rejected :
  ~ localTrace acceptMachine false [initial []].
Proof. simpl. discriminate. Qed.

Theorem premature_halt_rejected :
  ~ localTrace acceptMachine true [initial []; initial []].
Proof. simpl. intros [h _]. discriminate. Qed.

Theorem missing_halt_rejected :
  ~ localTrace loopMachine true [initial []].
Proof. simpl. discriminate. Qed.

Theorem two_step_accepts :
  localTrace moveThenAccept true [initial []; goodSuccessor].
Proof. split; reflexivity. Qed.

Theorem wrong_successor_halts :
  step moveThenAccept wrongSuccessor = inl true.
Proof. reflexivity. Qed.

(** The final configuration accepts, but its predecessor cannot reach it. *)
Theorem wrong_successor_rejected :
  ~ localTrace moveThenAccept true [initial []; wrongSuccessor].
Proof. simpl. intros [h _]. discriminate. Qed.

Theorem zero_clock_rejected : forall m c,
  ~ boundedTableau m c 0 true.
Proof.
  intros m c [trace [hhead [hbound _]]].
  destruct trace; simpl in *; [discriminate|lia].
Qed.

Theorem one_clock_accepts :
  boundedTableau acceptMachine (initial []) 1 true.
Proof.
  exists [initial []]. simpl. repeat split; auto.
Qed.

End Tableau.
