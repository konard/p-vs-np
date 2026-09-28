(* Issue #532, Idea 11: LP relaxation exactness (vertex cover integrality gap).

   Rocq counterpart of lean/Idea11.lean; theorem names are aligned.

   Fractional covers are measured in half units: x : nat -> nat with
   x i <= 2 (0, 1/2, 1) and x u + x v >= 2 on every edge of a graph on
   vertices < n; the LP value is sumTo x n / 2.  Integral covers are
   s : nat -> bool with cost card s n.
   Proved for every n (and every graph where stated):
   - half_feasible_complete, frac_lower_complete: the half-integral LP
     optimum of K_n is n/2 (n >= 2);
   - complete_cover_large, complete_cover_exact: the integral optimum of
     K_n is n - 1;
   - gap_family: on K_{2q} the gap is (2q - 1)/q = 2 - 1/q -> 2;
   - not_LPExact_complete: the relaxation is not exact on K_n, n >= 3;
   - rounding_two_approx: threshold rounding is a 2-approximation on every
     graph.
   Verdict: automatic LP exactness refuted by a general theorem; exact
   polynomial-size LPs for NP-hard polytopes refuted in full strength by
   Fiorini-Massar-Pokutta-Tiwary-de Wolf (not formalized).  Nothing here
   proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool.

Fixpoint sumTo (x : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => sumTo x n + x n
  end.

Definition ind (b : bool) : nat := if b then 1 else 0.

Definition card (s : nat -> bool) (n : nat) : nat := sumTo (fun i => ind (s i)) n.

Definition FracCover (n : nat) (adj : nat -> nat -> bool) (x : nat -> nat) : Prop :=
  (forall i, i < n -> x i <= 2) /\
  (forall u v, u < n -> v < n -> adj u v = true -> 2 <= x u + x v).

Definition IntCover (n : nat) (adj : nat -> nat -> bool) (s : nat -> bool) : Prop :=
  forall u v, u < n -> v < n -> adj u v = true -> s u = true \/ s v = true.

Definition complete (u v : nat) : bool := negb (Nat.eqb u v).

Lemma complete_ne : forall u v, u <> v -> complete u v = true.
Proof.
  intros u v h. unfold complete. apply negb_true_iff. apply Nat.eqb_neq. exact h.
Qed.

Theorem sumTo_le : forall x y n, (forall i, i < n -> x i <= y i) -> sumTo x n <= sumTo y n.
Proof.
  intros x y n. induction n as [|n IH]; intro h; simpl; [lia|].
  pose proof (IH (fun i hi => h i ltac:(lia))). pose proof (h n ltac:(lia)). lia.
Qed.

Theorem sumTo_const_le : forall x c n, (forall i, i < n -> c <= x i) -> c * n <= sumTo x n.
Proof.
  intros x c n. induction n as [|n IH]; intro h; simpl; [lia|].
  pose proof (IH (fun i hi => h i ltac:(lia))). pose proof (h n ltac:(lia)). nia.
Qed.

Theorem sumTo_except : forall x c u n, u < n ->
  (forall i, i < n -> i <> u -> c <= x i) -> c * (n - 1) <= sumTo x n.
Proof.
  intros x c u n. induction n as [|n IH]; intros hu h; [lia|].
  simpl. replace (n - 0) with n by lia.
  destruct (Nat.eq_dec u n) as [e|e].
  - pose proof (sumTo_const_le x c n (fun i hi => h i ltac:(lia) ltac:(lia))). lia.
  - pose proof (IH ltac:(lia) (fun i hi hne => h i ltac:(lia) hne)) as h1.
    pose proof (h n ltac:(lia) ltac:(lia)) as h2.
    destruct n as [|m]; [lia|].
    replace (S m - 1) with m in h1 by lia. nia.
Qed.

Theorem card_all : forall s n, (forall i, i < n -> s i = true) -> card s n = n.
Proof.
  intros s n. induction n as [|n IH]; intro h; [reflexivity|].
  unfold card in *. simpl. rewrite IH by (intros; apply h; lia).
  rewrite (h n ltac:(lia)). simpl. lia.
Qed.

(** On K_n the all-1/2 vector is a fractional cover of value n/2. *)
Theorem half_feasible_complete : forall n,
  FracCover n complete (fun _ => 1) /\ sumTo (fun _ => 1) n = n.
Proof.
  intro n. split; [split; intros; lia|].
  induction n as [|n IH]; simpl; lia.
Qed.

Theorem exists_zero_or_all_pos : forall x n,
  (exists u, u < n /\ x u = 0) \/ (forall i, i < n -> 1 <= x i).
Proof.
  intros x n. induction n as [|n IH].
  - right. intros; lia.
  - destruct IH as [[u [hu hx]] | h].
    + left. exists u. split; [lia | exact hx].
    + destruct (Nat.eq_dec (x n) 0) as [e|e].
      * left. exists n. split; [lia | exact e].
      * right. intros i hi. destruct (Nat.eq_dec i n) as [ei|ei].
        -- subst. lia.
        -- apply h. lia.
Qed.

(** For n >= 2 every half-integral fractional cover of K_n has value >= n/2. *)
Theorem frac_lower_complete : forall n, 2 <= n -> forall x,
  FracCover n complete x -> n <= sumTo x n.
Proof.
  intros n hn x [_ hx].
  destruct (exists_zero_or_all_pos x n) as [[u [hu h0]] | hall].
  - assert (h2 : forall i, i < n -> i <> u -> 2 <= x i).
    { intros i hi hne. pose proof (hx u i hu hi (complete_ne u i ltac:(lia))). lia. }
    pose proof (sumTo_except x 2 u n hu h2). lia.
  - pose proof (sumTo_const_le x 1 n hall). lia.
Qed.

(** Every integral vertex cover of K_n has at least n - 1 vertices. *)
Theorem complete_cover_large : forall s n, IntCover n complete s -> n <= card s n + 1.
Proof.
  intros s n. induction n as [|n IH]; intro h; [lia|].
  assert (hsub : IntCover n complete s).
  { intros u v hu hv ha. apply h; [lia | lia | exact ha]. }
  pose proof (IH hsub) as h1.
  destruct (s n) eqn:hs.
  - unfold card in *. simpl. rewrite hs. simpl. lia.
  - assert (hall : forall i, i < n -> s i = true).
    { intros i hi.
      destruct (h i n ltac:(lia) ltac:(lia) (complete_ne i n ltac:(lia))) as [h'|h'];
        [exact h' | congruence]. }
    pose proof (card_all s n hall) as hc.
    unfold card in *. simpl. rewrite hs. simpl. lia.
Qed.

Theorem card_nonzero : forall n, card (fun i => negb (Nat.eqb i 0)) (S n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  unfold card in *. simpl in *. rewrite IH. lia.
Qed.

(** The bound n - 1 is attained on K_n (every vertex except 0). *)
Theorem complete_cover_exact : forall n, 1 <= n ->
  IntCover n complete (fun i => negb (Nat.eqb i 0)) /\
  card (fun i => negb (Nat.eqb i 0)) n = n - 1.
Proof.
  intros n hn. split.
  - intros u v _ _ ha. unfold complete in ha.
    apply negb_true_iff, Nat.eqb_neq in ha.
    destruct u as [|u].
    + right. destruct v as [|v]; [lia | reflexivity].
    + left. reflexivity.
  - destruct n as [|m]; [lia|]. rewrite card_nonzero. lia.
Qed.

(** Integrality gap family: on K_{2q} the LP value is q while every
    integral cover has at least 2q - 1 vertices. *)
Theorem gap_family : forall q, 1 <= q ->
  FracCover (2 * q) complete (fun _ => 1) /\ sumTo (fun _ => 1) (2 * q) = 2 * q /\
  forall s, IntCover (2 * q) complete s -> 2 * q - 1 <= card s (2 * q).
Proof.
  intros q hq. destruct (half_feasible_complete (2 * q)) as [h1 h2].
  split; [exact h1|]. split; [exact h2|].
  intros s hs. pose proof (complete_cover_large s (2 * q) hs). lia.
Qed.

(** The relaxation is exact on a graph if every fractional value is matched
    by an integral cover of at most the same cost. *)
Definition LPExact (n : nat) (adj : nat -> nat -> bool) : Prop :=
  forall x, FracCover n adj x -> exists s, IntCover n adj s /\ 2 * card s n <= sumTo x n.

(** For every n >= 3 the vertex cover LP is not exact on K_n. *)
Theorem not_LPExact_complete : forall n, 3 <= n -> ~ LPExact n complete.
Proof.
  intros n hn h.
  destruct (half_feasible_complete n) as [hf hv].
  destruct (h _ hf) as [s [hs hc]].
  pose proof (complete_cover_large s n hs). rewrite hv in hc. lia.
Qed.

(** Threshold rounding: take every vertex with value at least 1/2. *)
Definition round (x : nat -> nat) (i : nat) : bool := Nat.leb 1 (x i).

(** Rounding is a 2-approximation against the LP on every graph. *)
Theorem rounding_two_approx : forall n adj x, FracCover n adj x ->
  IntCover n adj (round x) /\ card (round x) n <= sumTo x n.
Proof.
  intros n adj x [_ hx]. split.
  - intros u v hu hv ha. pose proof (hx u v hu hv ha) as H. unfold round.
    destruct (Nat.leb_spec 1 (x u)); [left; reflexivity|].
    right. apply Nat.leb_le. lia.
  - apply sumTo_le. intros i _. unfold round, ind.
    destruct (Nat.leb_spec 1 (x i)); lia.
Qed.
