(* Issue #532, Idea 36: exact relaxation and rounding.

   Rocq counterpart of ../lean/Idea36.lean (same theorem names and content).
   Half-unit vertex cover: x v in {0,1,2} means 0, 1/2, 1; a fractional cover
   has x u + x v >= 2 on every edge. Threshold rounding (x v >= 1) gives a
   vertex cover of size at most the LP value in halves (factor 2); the
   complete graph shows an integrality gap (LP n/2, integral n - 1), so no
   rounding of this relaxation is exact for n >= 3. In general, an exact
   rounding of a relaxation yields optimal solutions and decides the
   decision version.  ExactRoundingObligationFor is the generic schema (free
   PolyTime, feasible, cost, lp).

   Over the shared machine model (Complexity.Machine, time = step count of
   Complexity.Run), vertex-cover instances are words (budgetOf, edgesOf,
   verticesOf; a certificate cover is read by coverOf).  The open obligation
   ExactRoundingObligation asks for a polynomial-time machine map that keeps
   the instance and appends an optimal vertex cover.
   exactRoundingObligation_iff_schema shows it is exactly the schema
   instantiated with machine-computed roundings and some relaxation bound.
   exactRounding_inP and exactRounding_gives_pEqualsNP turn it into InP VC and
   PEqualsNP under the named known theorems CoverCheckInP and VCHard (stated
   as definitions and used only as explicit premises).

   Difference from Lean: Lean defines the languages VC and CoverCheck with
   classical decide.  Here they are computable Boolean functions (VC by brute
   force over the assignments of the vertices 0 .. vbound - 1), and vc_iff and
   coverCheck_iff prove they mean the same propositions as in Lean.  The Lean
   example on the triangle is the named Example vc_encoding_check.  All
   proofs are constructive; no axioms are used. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(** Generic schema (free [PolyTime], [feasible], [cost] and [lp], not a
    machine model): a relaxation bound together with an exact rounding in the
    class [PolyTime].  The machine instance for vertex cover is
    [ExactRoundingObligation] below. *)
Definition ExactRoundingObligationFor {Inst Sol : Type} (PolyTime : (Inst -> Sol) -> Prop)
    (feasible : Inst -> Sol -> Prop) (cost : Inst -> Sol -> nat) (lp : Inst -> nat) : Prop :=
  Relaxation feasible cost lp /\ exists rnd, PolyTime rnd /\ ExactRounding feasible cost lp rnd.

Example triangle_check :
  halfSum [0; 1; 2] (fun _ => 1) = 3 /\ cost [0; 1; 2] (round (fun _ => 1)) = 3.
Proof. split; reflexivity. Qed.

(* Vertex cover on the shared machine model.

   A word is read as a list of unary numbers (true^k false is k).  The list
   k, e, a1, b1, ..., ae, be, c0, c1, ... is the instance "is there a vertex
   cover of the edges (a1, b1), ..., (ae, be) with at most k vertices", and the
   trailing numbers c0, c1, ... (if any) are a candidate cover: vertex v is
   chosen iff cv <> 0.  The vertices are 0, ..., vbound - 1, where vbound
   exceeds every endpoint. *)

Fixpoint natsAux (w : Word) (k : nat) : list nat :=
  match w with
  | [] => []
  | true :: r => natsAux r (S k)
  | false :: r => k :: natsAux r 0
  end.

(** The unary numbers of a word. *)
Definition nats (w : Word) : list nat := natsAux w 0.

(** Encode a list of numbers in unary. *)
Fixpoint encNats (l : list nat) : Word :=
  match l with
  | [] => []
  | k :: r => repeat true k ++ false :: encNats r
  end.

Fixpoint toPairs (l : list nat) : list (nat * nat) :=
  match l with
  | a :: b :: r => (a, b) :: toPairs r
  | _ => []
  end.

(** One more than the largest endpoint. *)
Fixpoint vbound (es : list (nat * nat)) : nat :=
  match es with
  | [] => 0
  | e :: r => Nat.max (Nat.max (S (fst e)) (S (snd e))) (vbound r)
  end.

(** The budget [k] of the instance. *)
Definition budgetOf (w : Word) : nat := hd 0 (nats w).

(** The edges of the instance. *)
Definition edgesOf (w : Word) : list (nat * nat) :=
  toPairs (firstn (2 * nth 1 (nats w) 0) (skipn 2 (nats w))).

(** The vertices [0, ..., vbound - 1] of the instance. *)
Definition verticesOf (w : Word) : list nat := seq 0 (vbound (edgesOf w)).

(** The candidate cover carried after the instance. *)
Definition coverOf (w : Word) (v : nat) : bool :=
  negb (nth v (skipn (2 + 2 * nth 1 (nats w) 0) (nats w)) 0 =? 0).

(* The triangle with budget 2, and the cover {1, 2} appended. *)
Example vc_encoding_check :
  budgetOf (encNats [2; 3; 0; 1; 1; 2; 0; 2]) = 2 /\
  edgesOf (encNats [2; 3; 0; 1; 1; 2; 0; 2]) = [(0, 1); (1, 2); (0, 2)] /\
  verticesOf (encNats [2; 3; 0; 1; 1; 2; 0; 2]) = [0; 1; 2] /\
  (coverOf (encNats [2; 3; 0; 1; 1; 2; 0; 2; 0; 1; 1]) 0,
   coverOf (encNats [2; 3; 0; 1; 1; 2; 0; 2; 0; 1; 1]) 1,
   coverOf (encNats [2; 3; 0; 1; 1; 2; 0; 2; 0; 1; 1]) 2) = (false, true, true).
Proof. repeat split; reflexivity. Qed.

(* Boolean cover test and its meaning. *)

Definition isCoverb (edges : list (nat * nat)) (C : nat -> bool) : bool :=
  forallb (fun e => C (fst e) || C (snd e)) edges.

Lemma isCoverb_iff : forall edges C, isCoverb edges C = true <-> IsCover edges C.
Proof.
  intros edges C. unfold isCoverb, IsCover. rewrite forallb_forall.
  split; intros h e he; specialize (h e he); apply orb_true_iff; exact h.
Qed.

Lemma vbound_endpoints : forall edges e, In e edges ->
  fst e < vbound edges /\ snd e < vbound edges.
Proof.
  induction edges as [| e' r IH]; intros e he; [destruct he |].
  destruct he as [<- | he]; cbn [vbound]; [lia |].
  destruct (IH e he). lia.
Qed.

Lemma cost_congr : forall vs C C', (forall v, In v vs -> C v = C' v) ->
  cost vs C = cost vs C'.
Proof.
  unfold cost. induction vs as [| v vs IH]; intros C C' h; [reflexivity |]. simpl.
  rewrite <- (h v (or_introl eq_refl)).
  destruct (C v); simpl; rewrite (IH C C' (fun u hu => h u (or_intror hu))); reflexivity.
Qed.

Lemma isCover_congr : forall edges C C',
  (forall v, v < vbound edges -> C v = C' v) -> IsCover edges C -> IsCover edges C'.
Proof.
  intros edges C C' h hc e he. destruct (vbound_endpoints edges e he) as [h1 h2].
  rewrite <- (h _ h1), <- (h _ h2). exact (hc e he).
Qed.

(** An assignment of the instance's vertices is a cover within the budget. *)
Definition vcGood (w : Word) (C : nat -> bool) : bool :=
  isCoverb (edgesOf w) C && (cost (verticesOf w) C <=? budgetOf w).

(** The vertex-cover language: the instance has a cover within its budget
    (brute force over the assignments of the vertices). *)
Definition VC : Language := fun w =>
  existsb (fun v => vcGood w (toAssign v)) (allAssignments (vbound (edgesOf w))).

(** The certificate check: the appended candidate is a cover within the
    budget. *)
Definition CoverCheck : Language := fun u =>
  isCoverb (edgesOf u) (coverOf u) && (cost (verticesOf u) (coverOf u) <=? budgetOf u).

(* VC means the proposition that Lean's VC decides. *)
Theorem vc_iff : forall w, VC w = true <->
  exists C, IsCover (edgesOf w) C /\ cost (verticesOf w) C <= budgetOf w.
Proof.
  intro w. unfold VC. rewrite existsb_exists. split.
  - intros [v [_ hv]]. unfold vcGood in hv. apply andb_true_iff in hv.
    destruct hv as [h1 h2]. exists (toAssign v).
    split; [apply isCoverb_iff; exact h1 | apply Nat.leb_le; exact h2].
  - intros [C [hc hk]]. set (n := vbound (edgesOf w)).
    assert (hagree : forall i, i < n -> toAssign (prefixOf C n) i = C i).
    { intros i hi. apply toAssign_prefixOf. exact hi. }
    exists (prefixOf C n). split.
    + apply mem_allAssignments_iff. apply length_prefixOf.
    + unfold vcGood. apply andb_true_iff. split.
      * apply isCoverb_iff. apply (isCover_congr _ C); [| exact hc].
        intros v hv. symmetry. apply hagree. exact hv.
      * apply Nat.leb_le. rewrite <- hk. apply Nat.eq_le_incl. apply cost_congr.
        intros v hv. unfold verticesOf in hv. apply in_seq in hv.
        apply hagree. unfold n. lia.
Qed.

(* CoverCheck means the proposition that Lean's CoverCheck decides. *)
Theorem coverCheck_iff : forall u, CoverCheck u = true <->
  IsCover (edgesOf u) (coverOf u) /\ cost (verticesOf u) (coverOf u) <= budgetOf u.
Proof.
  intro u. unfold CoverCheck. rewrite andb_true_iff, isCoverb_iff, Nat.leb_le.
  reflexivity.
Qed.

(** Known theorem, not mechanised here.  Checking a proposed vertex cover
    against the budget takes polynomial time: this is the certificate check
    that puts vertex cover in NP (R. M. Karp, "Reducibility among
    combinatorial problems", 1972; Garey-Johnson, Computers and
    Intractability, 1979, section 3.1).  Used only as an explicit premise. *)
Definition CoverCheckInP : Prop := InP CoverCheck.

(** Known theorem, not mechanised here.  Vertex cover is NP-hard (Karp 1972,
    via SAT <= 3-SAT <= CLIQUE <= VERTEX COVER; Garey-Johnson 1979,
    Theorem 3.3).  Used only as an explicit premise. *)
Definition VCHard : Prop := NPHard VC.

(** [C] is a minimum vertex cover of [edges] on the vertex list [vs]. *)
Definition OptimalCover (edges : list (nat * nat)) (vs : list nat) (C : nat -> bool) : Prop :=
  IsCover edges C /\ forall C', IsCover edges C' -> cost vs C <= cost vs C'.

(** Open obligation (exact rounding for vertex cover, machine model).  A
    polynomial-time machine map [g] ([Computes m g p]: the step count of the
    run is at most [evalPoly p |w|]) that keeps the instance of [w] and
    appends an optimal vertex cover.  By [exactRoundingObligation_iff_schema]
    this is exactly an exact rounding, computed by a machine, of some
    relaxation bound. *)
Definition ExactRoundingObligation : Prop :=
  exists (m : Machine) (g : Word -> Word) (p : Polynomial), Computes m g p /\
    forall w, budgetOf (g w) = budgetOf w /\ edgesOf (g w) = edgesOf w /\
      OptimalCover (edgesOf w) (verticesOf w) (coverOf (g w)).

Theorem bool_eq_of_iff : forall a b : bool, (a = true <-> b = true) -> a = b.
Proof.
  intros [] [] h; try reflexivity.
  - symmetry. apply h. reflexivity.
  - apply h. reflexivity.
Qed.

(* Conditional theorem.  The obligation reduces vertex cover to the
   certificate check by a polynomial-time machine. *)
Theorem exactRounding_reduces : ExactRoundingObligation -> PolyReduces VC CoverCheck.
Proof.
  intros [m [g [p [hm hg]]]]. exists m, g, p. split; [exact hm |].
  intro w. apply bool_eq_of_iff. destruct (hg w) as [hb [he [hcov hopt]]].
  assert (hv : verticesOf (g w) = verticesOf w) by (unfold verticesOf; rewrite he; reflexivity).
  rewrite vc_iff, coverCheck_iff, hb, he, hv. split.
  - intros [C [hC hk]]. split; [exact hcov |]. eapply Nat.le_trans; [apply hopt; exact hC | exact hk].
  - intros [hC hk]. exists (coverOf (g w)). split; [exact hC | exact hk].
Qed.

(* Conditional theorem.  The obligation and the certificate check put vertex
   cover in P. *)
Theorem exactRounding_inP : ExactRoundingObligation -> CoverCheckInP -> InP VC.
Proof.
  intros h hc. exact (inP_of_reduces VC CoverCheck (exactRounding_reduces h) hc).
Qed.

(* Conditional theorem.  With NP-hardness of vertex cover, the obligation
   gives P = NP. *)
Theorem exactRounding_gives_pEqualsNP :
  VCHard -> CoverCheckInP -> ExactRoundingObligation -> PEqualsNP.
Proof.
  intros hard hc h L hL. exact (inP_of_reduces L VC (hard L hL) (exactRounding_inP h hc)).
Qed.

(* Non-vacuity (of the reduction the obligation provides).  Given the
   certificate check, not every language reduces to it: otherwise every
   language would be in P, contradicting exists_not_inP. *)
Theorem not_forall_reduces_coverCheck :
  CoverCheckInP -> ~ (forall L : Language, PolyReduces L CoverCheck).
Proof.
  intros hc hall. destruct exists_not_inP as [L hL].
  exact (hL (inP_of_reduces L CoverCheck (hall L) hc)).
Qed.

(* The machine obligation is the schema with machine-computed roundings. *)

(** Feasibility of vertex cover on word instances. *)
Definition vcFeasible (w : Word) (C : nat -> bool) : Prop := IsCover (edgesOf w) C.
(** Cost of vertex cover on word instances. *)
Definition vcCost (w : Word) (C : nat -> bool) : nat := cost (verticesOf w) C.

(** A rounding computed by a polynomial-time machine: the machine keeps the
    instance and appends the rounded cover. *)
Definition MachineRounding (rnd : Word -> nat -> bool) : Prop :=
  exists (m : Machine) (g : Word -> Word) (p : Polynomial), Computes m g p /\
    forall w, budgetOf (g w) = budgetOf w /\ edgesOf (g w) = edgesOf w /\
      rnd w = coverOf (g w).

(* Instantiation.  The machine obligation holds exactly when, for some
   relaxation bound lp, the schema ExactRoundingObligationFor holds with
   machine-computed roundings. *)
Theorem exactRoundingObligation_iff_schema :
  ExactRoundingObligation <->
    exists lp : Word -> nat, ExactRoundingObligationFor MachineRounding vcFeasible vcCost lp.
Proof.
  split.
  - intros [m [g [p [hm hg]]]].
    exists (fun w => vcCost w (coverOf (g w))). split.
    + intros w C hC. exact (proj2 (proj2 (proj2 (hg w))) C hC).
    + exists (fun w => coverOf (g w)). split.
      * exists m, g, p. split; [exact hm |].
        intro w. destruct (hg w) as [hb [he _]]. split; [exact hb | split; [exact he | reflexivity]].
      * intro w. split; [exact (proj1 (proj2 (proj2 (hg w)))) | apply Nat.le_refl].
  - intros [lp [hrel [rnd [[m [g [p [hm hg]]]] hex]]]].
    exists m, g, p. split; [exact hm |].
    intro w. destruct (hg w) as [hb [he hr]].
    split; [exact hb | split; [exact he | split]].
    + pose proof (proj1 (hex w)) as h. unfold vcFeasible in h. rewrite hr in h. exact h.
    + intros C hC.
      pose proof (exact_rounding_optimal vcFeasible vcCost lp rnd hrel hex w C hC) as h.
      unfold vcCost in h. rewrite hr in h. exact h.
Qed.
