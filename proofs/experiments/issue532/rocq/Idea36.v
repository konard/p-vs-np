(* Issue #532, Idea 36: exact relaxation and rounding.

   Rocq counterpart of ../lean/Idea36.lean (same theorem names and content).
   Half-unit vertex cover: x v in {0,1,2} means 0, 1/2, 1; a fractional cover
   has x u + x v >= 2 on every edge. Threshold rounding (x v >= 1) gives a
   vertex cover of size at most the LP value in halves (factor 2); the
   complete graph shows an integrality gap (LP n/2, integral n - 1), so no
   rounding of this relaxation is exact for n >= 3. In general, an exact
   rounding of a relaxation yields optimal solutions and decides the
   decision version. All proofs are constructive. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* Conditional witness transfer. *)

Theorem tested (Discrete Relaxed : Type)
  (feasible : Discrete -> Prop) (relaxed : Relaxed -> Prop)
  (round : Relaxed -> Discrete) :
  (forall y, relaxed y -> feasible (round y)) ->
  (exists y, relaxed y) -> exists x, feasible x.
Proof.
  intros Hround [y Hy]; exists (round y); apply Hround, Hy.
Qed.

(* Half-unit vertex cover. *)

Definition FracCover (edges : list (nat * nat)) (x : nat -> nat) : Prop :=
  forall e, In e edges -> 2 <= x (fst e) + x (snd e).

Definition IsCover (edges : list (nat * nat)) (C : nat -> bool) : Prop :=
  forall e, In e edges -> C (fst e) = true \/ C (snd e) = true.

Definition round (x : nat -> nat) (v : nat) : bool := 1 <=? x v.

Definition cost (vs : list nat) (C : nat -> bool) : nat := length (filter C vs).

Fixpoint halfSum (vs : list nat) (x : nat -> nat) : nat :=
  match vs with
  | [] => 0
  | v :: vs' => x v + halfSum vs' x
  end.

Theorem round_is_cover (edges : list (nat * nat)) (x : nat -> nat) :
  FracCover edges x -> IsCover edges (round x).
Proof.
  intros H e He. specialize (H e He). unfold round.
  destruct (1 <=? x (fst e)) eqn:E1.
  - left. reflexivity.
  - right. apply Nat.leb_gt in E1. apply Nat.leb_le. lia.
Qed.

Theorem round_cost_le (vs : list nat) (x : nat -> nat) :
  cost vs (round x) <= halfSum vs x.
Proof.
  unfold cost. induction vs as [|v vs IH]; simpl; [lia|].
  destruct (round x v) eqn:E; simpl.
  - unfold round in E. apply Nat.leb_le in E. lia.
  - lia.
Qed.

Definition toFrac (C : nat -> bool) (v : nat) : nat := if C v then 2 else 0.

Theorem toFrac_cover (edges : list (nat * nat)) (C : nat -> bool) :
  IsCover edges C -> FracCover edges (toFrac C).
Proof.
  intros H e He. unfold toFrac.
  destruct (H e He) as [H1|H1]; rewrite H1;
    destruct (C (fst e)), (C (snd e)); lia.
Qed.

Theorem halfSum_toFrac (vs : list nat) (C : nat -> bool) :
  halfSum vs (toFrac C) = 2 * cost vs C.
Proof.
  unfold cost. induction vs as [|v vs IH]; simpl; [reflexivity|].
  unfold toFrac at 1. destruct (C v); simpl; rewrite IH; lia.
Qed.

Theorem round_two_approx (vs : list nat) (edges : list (nat * nat)) (x : nat -> nat) :
  FracCover edges x ->
  (forall y, FracCover edges y -> halfSum vs x <= halfSum vs y) ->
  forall C, IsCover edges C ->
  IsCover edges (round x) /\ cost vs (round x) <= 2 * cost vs C.
Proof.
  intros Hx Hopt C HC. split; [apply round_is_cover; exact Hx|].
  pose proof (round_cost_le vs x) as H1.
  pose proof (Hopt (toFrac C) (toFrac_cover edges C HC)) as H2.
  rewrite halfSum_toFrac in H2. lia.
Qed.

(* Integrality gap on complete graphs. *)

Fixpoint completeEdges (vs : list nat) : list (nat * nat) :=
  match vs with
  | [] => []
  | v :: vs' => map (fun w => (v, w)) vs' ++ completeEdges vs'
  end.

Theorem cost_all_true (vs : list nat) (C : nat -> bool) :
  (forall w, In w vs -> C w = true) -> cost vs C = length vs.
Proof.
  unfold cost. induction vs as [|v vs IH]; simpl; intro H; [reflexivity|].
  rewrite (H v (or_introl eq_refl)). simpl. rewrite IH; [reflexivity|].
  intros w Hw. apply H. right. exact Hw.
Qed.

Theorem complete_cover_cost (vs : list nat) (C : nat -> bool) :
  IsCover (completeEdges vs) C -> length vs <= cost vs C + 1.
Proof.
  induction vs as [|v vs IH]; intro HC; simpl; [lia|].
  assert (Hrest : IsCover (completeEdges vs) C).
  { intros e He. apply HC. simpl. apply in_or_app. right. exact He. }
  specialize (IH Hrest). unfold cost in *. simpl.
  destruct (C v) eqn:Hv; simpl.
  - lia.
  - assert (Hall : forall w, In w vs -> C w = true).
    { intros w Hw.
      assert (Hmem : In (v, w) (completeEdges (v :: vs))).
      { simpl. apply in_or_app. left. apply in_map_iff. exists w. split; auto. }
      destruct (HC _ Hmem) as [H|H]; simpl in H; [congruence|exact H]. }
    pose proof (cost_all_true vs C Hall) as Hc. unfold cost in Hc. lia.
Qed.

Theorem halfSum_one (vs : list nat) : halfSum vs (fun _ => 1) = length vs.
Proof. induction vs as [|v vs IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Theorem complete_graph_gap (vs : list nat) :
  FracCover (completeEdges vs) (fun _ => 1) /\
  halfSum vs (fun _ => 1) = length vs /\
  forall C, IsCover (completeEdges vs) C -> length vs <= cost vs C + 1.
Proof.
  split; [intros e _; simpl; lia|].
  split; [apply halfSum_one | apply complete_cover_cost].
Qed.

Theorem no_exact_rounding (vs : list nat) :
  3 <= length vs ->
  exists x, FracCover (completeEdges vs) x /\
    forall C, IsCover (completeEdges vs) C -> halfSum vs x < 2 * cost vs C.
Proof.
  intro H3. exists (fun _ => 1). split; [intros e _; simpl; lia|].
  intros C HC. pose proof (complete_cover_cost vs C HC).
  rewrite halfSum_one. lia.
Qed.

(* Exact rounding in general. *)

Definition Relaxation {Inst Sol : Type} (feasible : Inst -> Sol -> Prop)
    (cost : Inst -> Sol -> nat) (lp : Inst -> nat) : Prop :=
  forall I s, feasible I s -> lp I <= cost I s.

Definition ExactRounding {Inst Sol : Type} (feasible : Inst -> Sol -> Prop)
    (cost : Inst -> Sol -> nat) (lp : Inst -> nat) (rnd : Inst -> Sol) : Prop :=
  forall I, feasible I (rnd I) /\ cost I (rnd I) <= lp I.

Theorem exact_rounding_optimal {Inst Sol : Type} (feasible : Inst -> Sol -> Prop)
    (cost : Inst -> Sol -> nat) (lp : Inst -> nat) (rnd : Inst -> Sol) :
  Relaxation feasible cost lp -> ExactRounding feasible cost lp rnd ->
  forall I s, feasible I s -> cost I (rnd I) <= cost I s.
Proof.
  intros Hrel Hex I s Hs. pose proof (proj2 (Hex I)). pose proof (Hrel I s Hs). lia.
Qed.

Theorem exact_rounding_decides {Inst Sol : Type} (feasible : Inst -> Sol -> Prop)
    (cost : Inst -> Sol -> nat) (lp : Inst -> nat) (rnd : Inst -> Sol) :
  Relaxation feasible cost lp -> ExactRounding feasible cost lp rnd ->
  forall I k, (exists s, feasible I s /\ cost I s <= k) <-> cost I (rnd I) <= k.
Proof.
  intros Hrel Hex I k. split.
  - intros [s [Hs Hk]].
    pose proof (exact_rounding_optimal feasible cost lp rnd Hrel Hex I s Hs). lia.
  - intro Hk. exists (rnd I). split; [exact (proj1 (Hex I)) | exact Hk].
Qed.

Definition ExactRoundingObligation {Inst Sol : Type} (PolyTime : (Inst -> Sol) -> Prop)
    (feasible : Inst -> Sol -> Prop) (cost : Inst -> Sol -> nat) (lp : Inst -> nat) : Prop :=
  Relaxation feasible cost lp /\ exists rnd, PolyTime rnd /\ ExactRounding feasible cost lp rnd.

Example triangle_check :
  halfSum [0; 1; 2] (fun _ => 1) = 3 /\ cost [0; 1; 2] (round (fun _ => 1)) = 3.
Proof. split; reflexivity. Qed.
