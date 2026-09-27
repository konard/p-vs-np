(* Issue #532, Idea 22: decision-to-search self-reduction for SAT.

   Rocq counterpart of lean/Idea22.lean.  For every decision procedure dec
   with Decides dec, the search that fixes the variables of vs one at a time
   returns a satisfying assignment of every satisfiable CNF whose variables
   lie in vs (search_correct), asks exactly length vs questions
   (search_calls), and costs at most length vs times a polynomial bound on
   the questions (searchCost_le).  The open obligation ExactPolyDecider
   (relative to a cost model) yields polynomial search (decision_to_search);
   a correct search yields a decider (search_gives_decider); an exponential
   exact decider exists unconditionally (satDec_correct), and the obligation
   is trivial in the zero cost model (zero_cost_trivial).
   Verdict: correct tool, insufficient alone. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(* ---------- SAT core ---------- *)

Record Lit := mkLit { var : nat; pos : bool }.

Definition lit_eq_dec : forall l1 l2 : Lit, {l1 = l2} + {l1 <> l2}.
Proof. decide equality; [apply bool_dec | apply Nat.eq_dec]. Defined.

Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition clause_eq_dec : forall C1 C2 : Clause, {C1 = C2} + {C1 <> C2} :=
  list_eq_dec lit_eq_dec.

Definition evalLit (a : Assignment) (l : Lit) : bool :=
  if pos l then a (var l) else negb (a (var l)).

Fixpoint evalClause (a : Assignment) (C : Clause) : bool :=
  match C with
  | [] => false
  | l :: C' => evalLit a l || evalClause a C'
  end.

Fixpoint evalCNF (a : Assignment) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | C :: phi' => evalClause a C && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a, evalCNF a phi = true.

Lemma evalClause_true_iff : forall a C,
  evalClause a C = true <-> exists l, In l C /\ evalLit a l = true.
Proof.
  intros a C. induction C as [|l C IH]; simpl.
  - split; [discriminate | intros [l [[] _]]].
  - rewrite orb_true_iff, IH. split.
    + intros [H|[l' [Hin H]]]; [exists l | exists l']; auto.
    + intros [l' [[Heq|Hin] H]]; [subst; left | right; exists l']; auto.
Qed.

Lemma evalCNF_true_iff : forall a phi,
  evalCNF a phi = true <-> forall C, In C phi -> evalClause a C = true.
Proof.
  intros a phi. induction phi as [|C phi IH]; simpl.
  - split; [intros _ C Hin; destruct Hin | auto].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] C' [Heq|Hin]; [subst|]; auto.
    + intros H. split; auto.
Qed.

(* ---------- Restriction ---------- *)

Fixpoint clauseHas (v : nat) (b : bool) (C : Clause) : bool :=
  match C with
  | [] => false
  | l :: C' => (Nat.eqb (var l) v && Bool.eqb (pos l) b) || clauseHas v b C'
  end.

Fixpoint removeVar (v : nat) (C : Clause) : Clause :=
  match C with
  | [] => []
  | l :: C' => if Nat.eqb (var l) v then removeVar v C' else l :: removeVar v C'
  end.

Fixpoint restrict (v : nat) (b : bool) (phi : CNF) : CNF :=
  match phi with
  | [] => []
  | C :: phi' =>
      if clauseHas v b C then restrict v b phi' else removeVar v C :: restrict v b phi'
  end.

Definition setVar (a : Assignment) (v : nat) (b : bool) : Assignment :=
  fun x => if Nat.eqb x v then b else a x.

Lemma evalClause_setVar : forall a v b C,
  evalClause (setVar a v b) C = clauseHas v b C || evalClause a (removeVar v C).
Proof.
  intros a v b C. induction C as [|l C IH]; [reflexivity|].
  cbn [evalClause clauseHas removeVar]. rewrite IH.
  destruct (Nat.eqb (var l) v) eqn:E.
  - cbn [andb].
    generalize (clauseHas v b C) as x. generalize (evalClause a (removeVar v C)) as y.
    intros y x. apply Nat.eqb_eq in E. unfold evalLit, setVar. rewrite E, Nat.eqb_refl.
    destruct (pos l), b, x, y; reflexivity.
  - cbn [andb orb evalClause].
    generalize (clauseHas v b C) as x. generalize (evalClause a (removeVar v C)) as y.
    intros y x. unfold evalLit, setVar. rewrite E.
    destruct (pos l), (a (var l)), x, y; reflexivity.
Qed.

Theorem eval_restrict : forall a v b phi,
  evalCNF a (restrict v b phi) = evalCNF (setVar a v b) phi.
Proof.
  intros a v b phi. induction phi as [|C phi IH]; [reflexivity|].
  cbn [evalCNF restrict]. rewrite evalClause_setVar.
  destruct (clauseHas v b C); cbn [evalCNF orb andb]; rewrite IH; reflexivity.
Qed.

Lemma evalClause_congr : forall a a' C,
  (forall l, In l C -> a (var l) = a' (var l)) -> evalClause a C = evalClause a' C.
Proof.
  intros a a' C H. induction C as [|l C IH]; [reflexivity|].
  cbn [evalClause]. rewrite IH by (intros l' Hl'; apply H; right; exact Hl').
  unfold evalLit. rewrite (H l (or_introl eq_refl)). reflexivity.
Qed.

Theorem eval_congr : forall a a' phi,
  (forall C l, In C phi -> In l C -> a (var l) = a' (var l)) ->
  evalCNF a phi = evalCNF a' phi.
Proof.
  intros a a' phi H. induction phi as [|C phi IH]; [reflexivity|].
  cbn [evalCNF]. rewrite IH by (intros C' l HC' Hl; apply (H C'); [right|]; auto).
  rewrite (evalClause_congr a a' C) by (intros l Hl; apply (H C); [left|]; auto).
  reflexivity.
Qed.

Lemma setVar_self : forall a v x, setVar a v (a v) x = a x.
Proof.
  intros a v x. unfold setVar. destruct (Nat.eqb x v) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst. reflexivity.
Qed.

Theorem sat_split : forall phi v,
  Satisfiable phi <-> Satisfiable (restrict v true phi) \/ Satisfiable (restrict v false phi).
Proof.
  intros phi v. split.
  - intros [a Ha].
    assert (Hr : evalCNF a (restrict v (a v) phi) = true).
    { rewrite eval_restrict. rewrite (eval_congr _ a); auto.
      intros C l _ _. apply setVar_self. }
    destruct (a v); [left|right]; exists a; exact Hr.
  - intros [[a Ha]|[a Ha]].
    + exists (setVar a v true). rewrite <- eval_restrict. exact Ha.
    + exists (setVar a v false). rewrite <- eval_restrict. exact Ha.
Qed.

(* ---------- Occurring variables ---------- *)

Definition VarsIn (phi : CNF) (vs : list nat) : Prop :=
  forall C l, In C phi -> In l C -> In (var l) vs.

Lemma mem_removeVar : forall v C l, In l (removeVar v C) -> In l C /\ var l <> v.
Proof.
  intros v C l. induction C as [|l' C IH]; cbn [removeVar]; [intros []|].
  destruct (Nat.eqb (var l') v) eqn:E.
  - intros H. destruct (IH H). split; [right|]; auto.
  - intros [H|H].
    + subst. split; [left; reflexivity|]. apply Nat.eqb_neq. exact E.
    + destruct (IH H). split; [right|]; auto.
Qed.

Lemma mem_restrict : forall v b phi C',
  In C' (restrict v b phi) -> exists C, In C phi /\ C' = removeVar v C.
Proof.
  intros v b phi C'. induction phi as [|C phi IH]; cbn [restrict]; [intros []|].
  destruct (clauseHas v b C).
  - intros H. destruct (IH H) as [D [HD E]]. exists D. split; [right|]; auto.
  - intros [H|H].
    + exists C. split; [left|]; auto.
    + destruct (IH H) as [D [HD E]]. exists D. split; [right|]; auto.
Qed.

Theorem restrict_vars : forall phi v vs b,
  VarsIn phi (v :: vs) -> VarsIn (restrict v b phi) vs.
Proof.
  intros phi v vs b H C' l HC' Hl.
  destruct (mem_restrict v b phi C' HC') as [C [HC E]]. subst C'.
  destruct (mem_removeVar v C l Hl) as [HlC Hne].
  destruct (H C l HC HlC) as [E|E]; [congruence | exact E].
Qed.

Theorem sat_no_vars : forall phi, VarsIn phi [] ->
  (Satisfiable phi <-> evalCNF (fun _ => false) phi = true).
Proof.
  intros phi H. split.
  - intros [a Ha]. rewrite (eval_congr _ a); auto.
    intros C l HC Hl. destruct (H C l HC Hl).
  - intros H'. exists (fun _ => false). exact H'.
Qed.

Fixpoint solve (vs : list nat) (phi : CNF) : bool :=
  match vs with
  | [] => evalCNF (fun _ => false) phi
  | v :: vs' => solve vs' (restrict v true phi) || solve vs' (restrict v false phi)
  end.

Theorem solve_correct : forall vs phi, VarsIn phi vs ->
  (solve vs phi = true <-> Satisfiable phi).
Proof.
  induction vs as [|v vs IH]; intros phi H.
  - cbn [solve]. rewrite sat_no_vars by exact H. reflexivity.
  - cbn [solve]. rewrite sat_split with (v := v), orb_true_iff.
    rewrite (IH _ (restrict_vars phi v vs true H)), (IH _ (restrict_vars phi v vs false H)).
    reflexivity.
Qed.

(* ---------- Size and variables ---------- *)

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | C :: phi' => length C + 1 + size phi'
  end.

Lemma length_removeVar_le : forall v C, length (removeVar v C) <= length C.
Proof.
  intros v C. induction C as [|l C IH]; cbn [removeVar length]; [lia|].
  destruct (Nat.eqb (var l) v); cbn [length]; lia.
Qed.

Theorem size_restrict_le : forall v b phi, size (restrict v b phi) <= size phi.
Proof.
  intros v b phi. induction phi as [|C phi IH]; cbn [restrict size]; [lia|].
  pose proof (length_removeVar_le v C).
  destruct (clauseHas v b C); cbn [size]; lia.
Qed.

Fixpoint varsOf (phi : CNF) : list nat :=
  match phi with
  | [] => []
  | C :: phi' => map var C ++ varsOf phi'
  end.

Theorem varsOf_spec : forall phi, VarsIn phi (varsOf phi).
Proof.
  intros phi. induction phi as [|D phi IH]; intros C l HC Hl; [destruct HC|].
  cbn [varsOf]. apply in_or_app. destruct HC as [E|E].
  - subst D. left. apply in_map. exact Hl.
  - right. exact (IH C l E Hl).
Qed.

Theorem varsOf_length_le : forall phi, length (varsOf phi) <= size phi.
Proof.
  intros phi. induction phi as [|C phi IH]; cbn [varsOf size length]; [lia|].
  rewrite length_app, length_map. lia.
Qed.

(* ---------- Deciders and the self-reduction ---------- *)

Definition Decides (dec : CNF -> bool) : Prop :=
  forall psi, dec psi = true <-> Satisfiable psi.

Fixpoint search (dec : CNF -> bool) (vs : list nat) (phi : CNF) : Assignment * nat :=
  match vs with
  | [] => ((fun _ => false), 0)
  | v :: vs' =>
      let b := dec (restrict v true phi) in
      let r := search dec vs' (restrict v b phi) in
      (setVar (fst r) v b, S (snd r))
  end.

Theorem search_correct : forall dec, Decides dec -> forall vs phi,
  VarsIn phi vs -> Satisfiable phi -> evalCNF (fst (search dec vs phi)) phi = true.
Proof.
  intros dec Hdec vs. induction vs as [|v vs IH]; intros phi Hv Hs.
  - cbn [search fst]. apply (sat_no_vars phi Hv). exact Hs.
  - assert (Hb : Satisfiable (restrict v (dec (restrict v true phi)) phi)).
    { destruct (dec (restrict v true phi)) eqn:E.
      - apply Hdec. exact E.
      - assert (Hn : ~ Satisfiable (restrict v true phi)).
        { intros Hsat. apply Hdec in Hsat. congruence. }
        destruct (proj1 (sat_split phi v) Hs) as [H1|H2]; [contradiction|exact H2]. }
    cbn [search fst]. rewrite <- eval_restrict.
    apply IH; [apply restrict_vars; exact Hv | exact Hb].
Qed.

Theorem search_calls : forall dec vs phi, snd (search dec vs phi) = length vs.
Proof.
  intros dec vs. induction vs as [|v vs IH]; intros phi; [reflexivity|].
  cbn [search snd length]. rewrite IH. reflexivity.
Qed.

Theorem search_decides : forall dec, Decides dec -> forall vs phi, VarsIn phi vs ->
  (evalCNF (fst (search dec vs phi)) phi = true <-> Satisfiable phi).
Proof.
  intros dec Hdec vs phi Hv. split.
  - intros H. exists (fst (search dec vs phi)). exact H.
  - apply search_correct; assumption.
Qed.

Definition fullSearch (dec : CNF -> bool) (phi : CNF) : Assignment * nat :=
  search dec (varsOf phi) phi.

Theorem fullSearch_correct : forall dec, Decides dec -> forall phi,
  Satisfiable phi -> evalCNF (fst (fullSearch dec phi)) phi = true.
Proof.
  intros dec Hdec phi Hs. apply search_correct; [exact Hdec | apply varsOf_spec | exact Hs].
Qed.

Theorem fullSearch_calls_le : forall dec phi, snd (fullSearch dec phi) <= size phi.
Proof.
  intros dec phi. unfold fullSearch. rewrite search_calls. apply varsOf_length_le.
Qed.

Theorem search_gives_decider : forall S : CNF -> Assignment,
  (forall phi, Satisfiable phi -> evalCNF (S phi) phi = true) ->
  Decides (fun phi => evalCNF (S phi) phi).
Proof.
  intros S HS phi. split.
  - intros H. exists (S phi). exact H.
  - apply HS.
Qed.

(* ---------- Costs ---------- *)

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

Lemma polyEval_mono : forall c k m n, m <= n -> polyEval c k m <= polyEval c k n.
Proof.
  intros c k m n H. unfold polyEval. apply Nat.mul_le_mono_l.
  apply Nat.pow_le_mono_l. lia.
Qed.

Lemma mul_polyEval_le : forall c k n, n * polyEval c k n <= polyEval c (k + 1) n.
Proof.
  intros c k n. unfold polyEval. rewrite Nat.pow_add_r, Nat.pow_1_r.
  replace (n * (c * (n + 1) ^ k)) with (c * (n + 1) ^ k * n) by ring.
  rewrite Nat.mul_assoc. apply Nat.mul_le_mono_l. lia.
Qed.

Fixpoint searchCost (dec : CNF -> bool) (cost : CNF -> nat) (vs : list nat) (phi : CNF) : nat :=
  match vs with
  | [] => 0
  | v :: vs' =>
      cost (restrict v true phi)
      + searchCost dec cost vs' (restrict v (dec (restrict v true phi)) phi)
  end.

Theorem searchCost_le : forall dec cost c k,
  (forall psi, cost psi <= polyEval c k (size psi)) ->
  forall vs phi, searchCost dec cost vs phi <= length vs * polyEval c k (size phi).
Proof.
  intros dec cost c k Hc vs. induction vs as [|v vs IH]; intros phi; [cbn; lia|].
  cbn [searchCost length].
  pose proof (Nat.le_trans _ _ _ (Hc (restrict v true phi))
    (polyEval_mono c k _ _ (size_restrict_le v true phi))) as H1.
  pose proof (Nat.le_trans _ _ _ (IH (restrict v (dec (restrict v true phi)) phi))
    (Nat.mul_le_mono_l _ _ (length vs)
      (polyEval_mono c k _ _ (size_restrict_le v (dec (restrict v true phi)) phi)))) as H2.
  lia.
Qed.

Definition CostModel : Type := (CNF -> bool) -> CNF -> nat.

(* Open obligation: an exact SAT decider of polynomially bounded cost. *)
Definition ExactPolyDecider (Cost : CostModel) : Prop :=
  exists dec c k, Decides dec /\ forall psi, Cost dec psi <= polyEval c k (size psi).

Definition PolySearch (Cost : CostModel) : Prop :=
  exists dec c k, forall phi,
    (Satisfiable phi -> evalCNF (fst (fullSearch dec phi)) phi = true) /\
    searchCost dec (Cost dec) (varsOf phi) phi <= polyEval c (k + 1) (size phi).

Theorem decision_to_search : forall Cost, ExactPolyDecider Cost -> PolySearch Cost.
Proof.
  intros Cost [dec [c [k [Hdec Hc]]]]. exists dec, c, k. intros phi. split.
  - apply fullSearch_correct. exact Hdec.
  - eapply Nat.le_trans; [apply (searchCost_le dec (Cost dec) c k Hc)|].
    eapply Nat.le_trans; [|apply mul_polyEval_le].
    apply Nat.mul_le_mono_r. apply varsOf_length_le.
Qed.

(* ---------- An unconditional (exponential) decider ---------- *)

Definition satDec (phi : CNF) : bool := solve (varsOf phi) phi.

Theorem satDec_correct : Decides satDec.
Proof.
  intros phi. unfold satDec. apply solve_correct. apply varsOf_spec.
Qed.

Theorem zero_cost_trivial : ExactPolyDecider (fun _ _ => 0).
Proof.
  exists satDec, 0, 0. split; [exact satDec_correct | intros; lia].
Qed.

Theorem unconditional_search : forall phi, Satisfiable phi ->
  evalCNF (fst (fullSearch satDec phi)) phi = true.
Proof.
  intros phi Hs. apply fullSearch_correct; [exact satDec_correct | exact Hs].
Qed.
