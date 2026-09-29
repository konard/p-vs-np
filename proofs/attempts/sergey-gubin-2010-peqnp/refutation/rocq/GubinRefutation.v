(* A sound audit of abstract LP claims previously attributed to Gubin.
   The paper's actual inequalities, projection and relabeling action have not
   been encoded. These examples are not a refutation of his formulation. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Lia.
Local Open Scope nat_scope.

Module GubinAudit.

Record LPProblem := {
  numVars : nat;
  feasible : (nat -> Q) -> Prop
}.

(* Equality is rational equality, restricted to the LP's variables. *)
Definition pointEq (lp : LPProblem) (x y : nat -> Q) : Prop :=
  forall i, i < numVars lp -> Qeq (x i) (y i).

Definition isVertex (lp : LPProblem) (x : nat -> Q) : Prop :=
  feasible lp x /\
  forall y z t, Qlt 0 t -> Qlt t 1 ->
    feasible lp y -> feasible lp z ->
    pointEq lp x (fun i => (t * y i + (1 - t) * z i)%Q) ->
    pointEq lp y x /\ pointEq lp z x.

Record ExtremePoint (lp : LPProblem) := {
  ep_point : nat -> Q;
  ep_vertex : isVertex lp ep_point
}.

Definition isIntegral (lp : LPProblem) (x : nat -> Q) : Prop :=
  forall i, i < numVars lp -> exists z : Z, Qeq (x i) (inject_Z z).

Record DirectedGraph := {
  numNodes : nat;
  edge : nat -> nat -> Prop
}.

(* The range and bijection fields make order a vertex permutation. The final
   successor uses modulo, so cycleEdges includes the closing edge. *)
Record ATSPTour (g : DirectedGraph) := {
  order : nat -> nat;
  order_range : forall i, i < numNodes g -> order i < numNodes g;
  order_injective : forall i j, i < numNodes g -> j < numNodes g ->
    order i = order j -> i = j;
  order_surjective : forall j, j < numNodes g ->
    exists i, i < numNodes g /\ order i = j;
  cycleEdges : forall i, i < numNodes g ->
    edge g (order i) (order ((S i) mod numNodes g))
}.

Definition HasIntegralCorrespondence (g : DirectedGraph) (lp : LPProblem)
    (encode : ATSPTour g -> nat -> Q) : Prop :=
  (forall tour, exists ep : ExtremePoint lp,
    pointEq lp (ep_point lp ep) (encode tour) /\
    isIntegral lp (ep_point lp ep)) /\
  (forall ep : ExtremePoint lp,
    isIntegral lp (ep_point lp ep) ->
    exists tour, pointEq lp (encode tour) (ep_point lp ep)).

Definition isCoordinateSymmetric (lp : LPProblem) : Prop :=
  forall sigma : nat -> nat,
    (forall i, i < numVars lp -> sigma i < numVars lp) ->
    (forall i j, i < numVars lp -> j < numVars lp ->
      sigma i = sigma j -> i = j) ->
    (forall j, j < numVars lp ->
      exists i, i < numVars lp /\ sigma i = j) ->
    forall x, feasible lp x -> feasible lp (fun i => x (sigma i)).

Definition halfPoint (i : nat) : Q :=
  if Nat.eq_dec i 0 then 1 # 2 else 0.

(* The two linear equations x_0 = 1/2 and x_1 = 0. *)
Definition halfLP : LPProblem :=
  {| numVars := 2;
     feasible := fun x => Qeq (x 0) (1 # 2) /\ Qeq (x 1) 0 |}.

Lemma half_feasible : feasible halfLP halfPoint.
Proof. split; reflexivity. Qed.

Lemma half_unique : forall x, feasible halfLP x -> pointEq halfLP x halfPoint.
Proof.
  intros x [h0 h1] i hi.
  destruct i as [|i]; [exact h0|].
  destruct i as [|i]; [exact h1|].
  simpl in hi; lia.
Qed.

Lemma half_vertex : isVertex halfLP halfPoint.
Proof.
  split; [exact half_feasible|].
  intros y z t _ _ hy hz _.
  split; [exact (half_unique y hy)|exact (half_unique z hz)].
Qed.

Lemma half_not_integral : ~ isIntegral halfLP halfPoint.
Proof.
  intro h.
  destruct (h 0 ltac:(simpl; lia)) as [z hz].
  unfold halfPoint in hz; simpl in hz.
  unfold Qeq, inject_Z in hz; simpl in hz.
  lia.
Qed.

Theorem fractional_vertex_exists :
  exists lp : LPProblem, exists ep : ExtremePoint lp,
    ~ isIntegral lp (ep_point lp ep).
Proof.
  exists halfLP, {| ep_point := halfPoint; ep_vertex := half_vertex |}.
  exact half_not_integral.
Qed.

Definition swap (i : nat) : nat := if Nat.eq_dec i 0 then 1 else 0.

Lemma half_asymmetric : ~ isCoordinateSymmetric halfLP.
Proof.
  intro hs.
  assert (hrange : forall i, i < numVars halfLP -> swap i < numVars halfLP).
  { intros i hi. unfold swap. destruct (Nat.eq_dec i 0); simpl; lia. }
  assert (hinj : forall i j, i < numVars halfLP -> j < numVars halfLP ->
                    swap i = swap j -> i = j).
  { intros i j hi hj heq.
    assert (i = 0 \/ i = 1) as hi' by (simpl in hi; lia).
    assert (j = 0 \/ j = 1) as hj' by (simpl in hj; lia).
    destruct hi' as [hi'|hi']; destruct hj' as [hj'|hj']; subst;
    unfold swap in heq; simpl in heq; lia. }
  assert (hsurj : forall j, j < numVars halfLP ->
    exists i, i < numVars halfLP /\ swap i = j).
  { intros j hj. assert (j = 0 \/ j = 1) as h by (simpl in hj; lia).
    destruct h as [h|h]; subst j.
    - exists 1; split; [simpl; lia|reflexivity].
    - exists 0; split; [simpl; lia|reflexivity]. }
  pose proof (hs swap hrange hinj hsurj halfPoint half_feasible) as h.
  destruct h as [h0 _].
  unfold swap, halfPoint in h0; simpl in h0.
  unfold Qeq in h0; simpl in h0.
  lia.
Qed.

Theorem asymmetry_does_not_imply_integrality :
  exists lp : LPProblem, ~ isCoordinateSymmetric lp /\
    exists ep : ExtremePoint lp, ~ isIntegral lp (ep_point lp ep).
Proof.
  exists halfLP. split; [exact half_asymmetric|].
  exists {| ep_point := halfPoint; ep_vertex := half_vertex |}.
  exact half_not_integral.
Qed.

Definition noEdgeGraph : DirectedGraph :=
  {| numNodes := 1; edge := fun _ _ => False |}.

Lemma no_tour : ATSPTour noEdgeGraph -> False.
Proof.
  intro tour.
  exact (cycleEdges noEdgeGraph tour 0 ltac:(simpl; lia)).
Qed.

Definition zeroPoint (_ : nat) : Q := 0.
Definition zeroLP : LPProblem :=
  {| numVars := 1; feasible := fun x => Qeq (x 0) 0 |}.

Lemma zero_unique : forall x, feasible zeroLP x -> pointEq zeroLP x zeroPoint.
Proof.
  intros x hx i hi.
  assert (i = 0) as -> by (simpl in hi; lia).
  exact hx.
Qed.

Lemma zero_vertex : isVertex zeroLP zeroPoint.
Proof.
  split; [reflexivity|].
  intros y z t _ _ hy hz _.
  split; [exact (zero_unique y hy)|exact (zero_unique z hz)].
Qed.

Lemma zero_integral : isIntegral zeroLP zeroPoint.
Proof.
  intros i hi. exists 0%Z. reflexivity.
Qed.

Theorem abstract_correspondence_can_fail :
  forall encode : ATSPTour noEdgeGraph -> nat -> Q,
    ~ HasIntegralCorrespondence noEdgeGraph zeroLP encode.
Proof.
  intros encode [_ backward].
  destruct (backward {| ep_point := zeroPoint; ep_vertex := zero_vertex |}
    zero_integral) as [tour _].
  exact (no_tour tour).
Qed.

End GubinAudit.
