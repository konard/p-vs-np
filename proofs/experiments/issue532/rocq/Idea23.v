(* Issue #532, Idea 23: resolution and the Cook-Reckhow framework.

   Rocq counterpart of lean/Idea23.lean.  Resolution with weakening is
   sound (derives_sound, empty_derivable_unsat) and complete for every CNF
   (lift, resolution_complete, unsat_iff_derives_empty).  Abstract
   Cook-Reckhow proof systems: polynomial boundedness gives a short
   certificate characterisation of UNSAT (bounded_certificate); an exact
   decider gives a trivially bounded system (fromDecider_bounded), so the
   open obligation NoPolyBoundedProofSystem must restrict to efficient
   verifiers (unrestricted_obligation_false); under the obligation, efficient
   exact deciders are excluded (lower_bound_excludes_efficient_decider).
   Verdict: resolution refuted in full strength as a polynomial method
   (Haken 1985, cited, not formalized); Cook's program developed to an open
   obligation. *)

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

Definition Decides (dec : CNF -> bool) : Prop :=
  forall psi, dec psi = true <-> Satisfiable psi.

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

Definition satDec (phi : CNF) : bool := solve (varsOf phi) phi.

Theorem satDec_correct : Decides satDec.
Proof.
  intros phi. unfold satDec. apply solve_correct. apply varsOf_spec.
Qed.

(* ---------- Resolution ---------- *)

Inductive Derives (phi : CNF) : Clause -> Prop :=
  | d_ax : forall C, In C phi -> Derives phi C
  | d_res : forall v C1 C2,
      Derives phi (mkLit v true :: C1) -> Derives phi (mkLit v false :: C2) ->
      Derives phi (C1 ++ C2)
  | d_weak : forall C D, Derives phi C -> (forall l, In l C -> In l D) -> Derives phi D.

Theorem derives_sound : forall phi C, Derives phi C ->
  forall a, evalCNF a phi = true -> evalClause a C = true.
Proof.
  intros phi C H a Ha. induction H as [C HC | v C1 C2 _ IH1 _ IH2 | C D _ IH Hsub].
  - rewrite evalCNF_true_iff in Ha. apply Ha. exact HC.
  - apply evalClause_true_iff in IH1. apply evalClause_true_iff in IH2.
    apply evalClause_true_iff.
    destruct IH1 as [l1 [Hl1 E1]]. destruct IH2 as [l2 [Hl2 E2]].
    destruct Hl1 as [R1|R1].
    + destruct Hl2 as [R2|R2].
      * subst l1 l2. unfold evalLit in E1, E2. cbn [pos var] in E1, E2.
        rewrite E1 in E2. discriminate.
      * exists l2. split; [apply in_or_app; right; exact R2 | exact E2].
    + exists l1. split; [apply in_or_app; left; exact R1 | exact E1].
  - apply evalClause_true_iff in IH. apply evalClause_true_iff.
    destruct IH as [l [Hl E]]. exists l. split; [apply Hsub; exact Hl | exact E].
Qed.

Theorem empty_derivable_unsat : forall phi, Derives phi [] -> ~ Satisfiable phi.
Proof.
  intros phi H [a Ha]. pose proof (derives_sound phi [] H a Ha) as E. discriminate.
Qed.

Lemma mem_restrict_full : forall v b phi C',
  In C' (restrict v b phi) ->
  exists C, In C phi /\ clauseHas v b C = false /\ C' = removeVar v C.
Proof.
  intros v b phi C'. induction phi as [|C phi IH]; cbn [restrict]; [intros []|].
  destruct (clauseHas v b C) eqn:Hc.
  - intros H. destruct (IH H) as [D [HD [Hf E]]]. exists D. split; [right|]; auto.
  - intros [H|H].
    + exists C. split; [left; reflexivity|]. split; [exact Hc|symmetry; exact H].
    + destruct (IH H) as [D [HD [Hf E]]]. exists D. split; [right|]; auto.
Qed.

Lemma clauseHas_false : forall v b C, clauseHas v b C = false ->
  forall l, In l C -> var l = v -> pos l = negb b.
Proof.
  intros v b C. induction C as [|l' C IH]; intros H l Hl Hv; [destruct Hl|].
  cbn [clauseHas] in H. apply orb_false_iff in H. destruct H as [H1 H2].
  destruct Hl as [E|E].
  - subst l'. rewrite Hv, Nat.eqb_refl in H1. cbn [andb] in H1.
    destruct (pos l), b; cbn in H1 |- *; congruence.
  - exact (IH H2 l E Hv).
Qed.

Lemma mem_removeVar_of : forall v C l, In l C -> var l <> v -> In l (removeVar v C).
Proof.
  intros v C l. induction C as [|l' C IH]; intros Hl Hv; [destruct Hl|].
  cbn [removeVar]. destruct (Nat.eqb (var l') v) eqn:E.
  - destruct Hl as [H|H].
    + subst l'. apply Nat.eqb_eq in E. contradiction.
    + exact (IH H Hv).
  - destruct Hl as [H|H]; [left; exact H | right; exact (IH H Hv)].
Qed.

Theorem lift : forall v b phi D, Derives (restrict v b phi) D ->
  Derives phi (mkLit v (negb b) :: D).
Proof.
  intros v b phi D H.
  induction H as [D HD | w C1 C2 _ IH1 _ IH2 | C D _ IH Hsub].
  - destruct (mem_restrict_full v b phi D HD) as [C [HC [Hf E]]]. subst D.
    apply (d_weak phi C); [apply d_ax; exact HC|].
    intros l Hl. destruct (Nat.eq_dec (var l) v) as [Hv|Hv].
    + left. pose proof (clauseHas_false v b C Hf l Hl Hv) as Hp.
      destruct l as [lv lp]. cbn [var pos] in Hv, Hp. subst. reflexivity.
    + right. apply mem_removeVar_of; assumption.
  - assert (D1 : Derives phi (mkLit w true :: (mkLit v (negb b) :: C1))).
    { apply (d_weak phi _ _ IH1). intros x [H|[H|H]]; cbn; auto. }
    assert (D2 : Derives phi (mkLit w false :: (mkLit v (negb b) :: C2))).
    { apply (d_weak phi _ _ IH2). intros x [H|[H|H]]; cbn; auto. }
    apply (d_weak phi _ _ (d_res phi w _ _ D1 D2)).
    intros x Hx. apply in_app_or in Hx. destruct Hx as [[H|H]|[H|H]].
    + left. exact H.
    + right. apply in_or_app. left. exact H.
    + left. exact H.
    + right. apply in_or_app. right. exact H.
  - apply (d_weak phi _ _ IH). intros x [H|H]; [left; exact H | right; apply Hsub; exact H].
Qed.

Theorem resolution_complete : forall vs phi, VarsIn phi vs -> ~ Satisfiable phi ->
  Derives phi [].
Proof.
  induction vs as [|v vs IH]; intros phi Hv Hu.
  - destruct phi as [|C phi].
    + exfalso. apply Hu. exists (fun _ => false). reflexivity.
    + destruct C as [|l C].
      * apply d_ax. left. reflexivity.
      * exfalso. exact (Hv (l :: C) l (or_introl eq_refl) (or_introl eq_refl)).
  - assert (H1 : ~ Satisfiable (restrict v true phi)).
    { intros H. apply Hu. apply (sat_split phi v). left. exact H. }
    assert (H0 : ~ Satisfiable (restrict v false phi)).
    { intros H. apply Hu. apply (sat_split phi v). right. exact H. }
    pose proof (lift v true phi [] (IH _ (restrict_vars phi v vs true Hv) H1)) as D1.
    pose proof (lift v false phi [] (IH _ (restrict_vars phi v vs false Hv) H0)) as D0.
    exact (d_res phi v [] [] D0 D1).
Qed.

Theorem unsat_iff_derives_empty : forall phi, ~ Satisfiable phi <-> Derives phi [].
Proof.
  intros phi. split.
  - apply resolution_complete with (vs := varsOf phi). apply varsOf_spec.
  - apply empty_derivable_unsat.
Qed.

(* ---------- Cook-Reckhow proof systems ---------- *)

Record ProofSystem := mkPS {
  verify : list bool -> CNF -> bool;
  ps_sound : forall pi phi, verify pi phi = true -> ~ Satisfiable phi;
  ps_complete : forall phi, ~ Satisfiable phi -> exists pi, verify pi phi = true
}.

Definition PolyBounded (P : ProofSystem) : Prop :=
  exists c k, forall phi, ~ Satisfiable phi ->
    exists pi : list bool, length pi <= polyEval c k (size phi) /\ verify P pi phi = true.

Theorem bounded_certificate : forall P, PolyBounded P ->
  exists c k, forall phi, ~ Satisfiable phi <->
    exists pi : list bool, length pi <= polyEval c k (size phi) /\ verify P pi phi = true.
Proof.
  intros P [c [k Hb]]. exists c, k. intros phi. split.
  - apply Hb.
  - intros [pi [_ Hv]]. exact (ps_sound P pi phi Hv).
Qed.

Lemma fromDecider_sound : forall dec, Decides dec ->
  forall (pi : list bool) phi, negb (dec phi) = true -> ~ Satisfiable phi.
Proof.
  intros dec H pi phi Hv Hs. apply H in Hs. rewrite Hs in Hv. discriminate.
Qed.

Lemma fromDecider_complete : forall dec, Decides dec ->
  forall phi, ~ Satisfiable phi -> exists pi : list bool, negb (dec phi) = true.
Proof.
  intros dec H phi Hu. exists []. destruct (dec phi) eqn:E; [|reflexivity].
  exfalso. apply Hu. apply H. exact E.
Qed.

Definition fromDecider (dec : CNF -> bool) (H : Decides dec) : ProofSystem :=
  mkPS (fun _ phi => negb (dec phi)) (fromDecider_sound dec H) (fromDecider_complete dec H).

Theorem fromDecider_bounded : forall dec (H : Decides dec), PolyBounded (fromDecider dec H).
Proof.
  intros dec H. exists 0, 0. intros phi Hu.
  destruct (fromDecider_complete dec H phi Hu) as [pi Hpi].
  exists []. split; [cbn; lia | exact Hpi].
Qed.

(* Open obligation (Cook's program). *)
Definition NoPolyBoundedProofSystem (Efficient : ProofSystem -> Prop) : Prop :=
  forall P, Efficient P -> ~ PolyBounded P.

Theorem unrestricted_obligation_false : ~ NoPolyBoundedProofSystem (fun _ => True).
Proof.
  intros H. apply (H (fromDecider satDec satDec_correct) I).
  apply fromDecider_bounded.
Qed.

Theorem lower_bound_excludes_efficient_decider :
  forall (Efficient : ProofSystem -> Prop) (EffDec : (CNF -> bool) -> Prop),
  (forall dec (H : Decides dec), EffDec dec -> Efficient (fromDecider dec H)) ->
  NoPolyBoundedProofSystem Efficient ->
  forall dec, Decides dec -> ~ EffDec dec.
Proof.
  intros Efficient EffDec Hclosed Hlb dec H He.
  exact (Hlb _ (Hclosed dec H He) (fromDecider_bounded dec H)).
Qed.
