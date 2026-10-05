From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue568.rocq Require Import Tableau.
Import ListNotations.

Module Window.
Import Complexity Tableau.

Fixpoint pad (k : nat) (l : list Symbol) : list Symbol :=
  match k, l with
  | 0, _ => []
  | S k, [] => blank :: pad k []
  | S k, a :: rest => a :: pad k rest
  end.

Lemma pad_length : forall k l, length (pad k l) = k.
Proof. induction k; intros []; simpl; auto. Qed.

Lemma pad_pad : forall k w l, k <= w -> pad k (pad w l) = pad k l.
Proof.
  induction k; intros w l h; [reflexivity|].
  destruct w; [lia|]. destruct l; simpl; f_equal; apply IHk; lia.
Qed.

Lemma pad_cons_pad : forall k w a l, k <= S w ->
  pad k (a :: pad w l) = pad k (a :: l).
Proof.
  intros [|k] w a l h; simpl; [reflexivity|].
  f_equal. apply pad_pad. lia.
Qed.

Lemma pad_blank : forall k, pad k [blank] = pad k [].
Proof. intros []; reflexivity. Qed.

Definition window (k : nat) (c : Config) : Config :=
  {| state := state c; tapeLeft := pad k (tapeLeft c);
     tapeHead := tapeHead c; tapeRight := pad k (tapeRight c) |}.

(** Each move consumes at most one boundary cell. Missing cells are blanks. *)
Theorem window_move : forall k c q s d,
  window k (moveHead (window (S k) c) q s d) =
  window k (moveHead c q s d).
Proof.
  intros k [state l head r] q s d.
  destruct d; destruct l; destruct r;
    unfold window, moveHead; simpl;
    f_equal; try (apply pad_pad; lia);
    try (rewrite pad_cons_pad by lia; apply pad_blank);
    try (apply pad_cons_pad; lia).
  all: destruct k; simpl; [reflexivity|]; f_equal;
    first [change (pad k (pad (S (S k)) []) = pad k []); apply pad_pad; lia
          | apply (pad_cons_pad k (S k)); lia].
Qed.

Definition next (m : Machine) (k : nat) (c : bool + Config) : bool + Config :=
  match c with
  | inl b => inl b
  | inr c => match step m c with
      | inl b => inl b
      | inr d => inr (window k d)
      end
  end.

(** Halts are absorbing and the final halt instruction is charged. *)
Fixpoint runWindow (m : Machine) (t k : nat) (c : bool + Config) : bool + Config :=
  match t with
  | 0 => c
  | S t => runWindow m t (k - 1) (next m (k - 1) c)
  end.

Lemma window_step : forall m k c,
  next m k (inr (window (S k) c)) =
  match step m c with
  | inl b => inl b
  | inr d => inr (window k d)
  end.
Proof.
  intros m k c. unfold next, step.
  cbn [window state tapeHead].
  destruct (instruction m (state c) (tapeHead c)); [reflexivity|].
  f_equal. apply window_move.
Qed.

Lemma runWindow_halt : forall m t k b, runWindow m t k (inl b) = inl b.
Proof. intros m t. induction t; intros; simpl; auto. Qed.

Theorem runWindow_correct : forall m c t b, Run m c t b ->
  forall clock k, t <= clock -> clock <= k ->
  runWindow m clock k (inr (window k c)) = inl b.
Proof.
  intros m c t b hr. induction hr as [c b hs|c d t b hs hr IH];
    intros [|clock] [|k] ht hk; try lia;
    cbn [runWindow]; replace (S k - 1) with k by lia;
    rewrite window_step, hs.
  - apply runWindow_halt.
  - apply IH; lia.
Qed.

Theorem runWindow_of_localTrace : forall m c trace b clock k,
  hd_error trace = Some c -> localTrace m b trace ->
  length trace <= clock -> clock <= k ->
  runWindow m clock k (inr (window k c)) = inl b.
Proof.
  intros m c trace b clock k hhead hlocal ht hk.
  apply runWindow_correct with (t := length trace); auto.
  apply (proj1 (localTrace_iff_run m c (length trace) b)).
  exists trace. auto.
Qed.

End Window.
