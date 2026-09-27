(* Issue #532, Idea 23: resolution and the Cook-Reckhow framework.

   Rocq counterpart of lean/Idea23.lean.  Resolution with weakening is
   sound (derives_sound, empty_derivable_unsat) and complete for every CNF
   (lift, resolution_complete, unsat_iff_derives_empty).  Abstract
   Cook-Reckhow proof systems: polynomial boundedness gives a short
   certificate characterisation of UNSAT (bounded_certificate); an exact
   decider gives a trivially bounded system (fromDecider_bounded), so the
   generic schema NoPolyBoundedProofSystemFor must restrict to efficient
   verifiers (unrestricted_obligation_false); under the schema, efficient
   exact deciders are excluded (lower_bound_excludes_efficient_decider).

   Machine part (shared model, Machines.v): a proof system is a
   VerifierProgram with a polynomial clock (MachineProofSystem); a
   polynomially bounded one puts its language in NP (inNP_of_polyBounded);
   every language in P has one (proofSystem_of_inP); some language has none
   (exists_noPolyBounded).  The open obligation NoPolyBoundedUNSATProofSystem
   gives ~ InP SAT, P <> NP given SATInNP, and is equivalent to NP <> coNP
   given the named known theorems CookReckhowNP, NPClosedUnderReductions,
   SATInNP and SATHard (noPolyBounded_iff_npNeCoNP).

   Verdict: resolution refuted in full strength as a polynomial method
   (Haken 1985, cited, not formalized); Cook's program developed to an open
   obligation.

   Differences from Lean:
   - The CNF core (Lit, Clause, CNF, evalLit, ...) is local to this file and
     shadows the SAT encoding layer of Machines.v, exactly as the Lean file
     uses its own namespace; SAT itself is Machines.SAT.
   - Derives constructors are d_ax, d_res, d_weak; ProofSystem fields are
     verify, ps_sound, ps_complete.
   - MachineProofSystem fields are verifier, timeBound, halts, mps_sound,
     mps_complete; Lean's MachineProofSystem.PolyBounded is
     MachinePolyBounded here (PolyBounded is the abstract notion).
   - Lean's verifierLanguage v is noncomputable (classical decide of an
     unbounded search over proofs).  Here verifierLanguage v p q is the
     computable bounded search: some proof of length <= q(|x|) is accepted
     by the step-bounded interpreter within timeLimit v p x pi steps.
     verifierLanguage_eq is stated pointwise and for a proof system whose
     polynomial bound is q.  exists_noPolyBounded is proved by a direct
     pointwise diagonal over encoded triples (verifier, clock, proof bound)
     instead of the Cantor family lemma. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(** Generic schema over a free efficiency notion Efficient: no proof system
    satisfying Efficient is polynomially bounded.  Its truth depends on the
    choice of Efficient (unrestricted_obligation_false); the machine version
    is NoPolyBoundedUNSATProofSystem below. *)
Definition NoPolyBoundedProofSystemFor (Efficient : ProofSystem -> Prop) : Prop :=
  forall P, Efficient P -> ~ PolyBounded P.

Theorem unrestricted_obligation_false : ~ NoPolyBoundedProofSystemFor (fun _ => True).
Proof.
  intros H. apply (H (fromDecider satDec satDec_correct) I).
  apply fromDecider_bounded.
Qed.

Theorem lower_bound_excludes_efficient_decider :
  forall (Efficient : ProofSystem -> Prop) (EffDec : (CNF -> bool) -> Prop),
  (forall dec (H : Decides dec), EffDec dec -> Efficient (fromDecider dec H)) ->
  NoPolyBoundedProofSystemFor Efficient ->
  forall dec, Decides dec -> ~ EffDec dec.
Proof.
  intros Efficient EffDec Hclosed Hlb dec H He.
  exact (Hlb _ (Hclosed dec H He) (fromDecider_bounded dec H)).
Qed.

(* ---------- Machine part: Cook-Reckhow proof systems in the shared model ---------- *)

(** A Cook-Reckhow proof system for L in the shared machine model: a verifier
    program that halts within the polynomial timeBound on every (input, proof)
    pair, is sound for L, and is complete for L. *)
Record MachineProofSystem (L : Language) := {
  verifier : VerifierProgram;
  timeBound : Polynomial;
  halts : forall x pi, exists t b,
    t <= timeLimit verifier timeBound x pi /\ verifierRun verifier x pi t b;
  mps_sound : forall x pi t, verifierRun verifier x pi t true -> L x = true;
  mps_complete : forall x, L x = true -> exists pi t, verifierRun verifier x pi t true
}.
Arguments verifier {L} _.
Arguments timeBound {L} _.
Arguments halts {L} _ _ _.
Arguments mps_sound {L} _ _ _ _ _.
Arguments mps_complete {L} _ _ _.

(** Polynomial boundedness (Lean: MachineProofSystem.PolyBounded): every
    member has an accepted proof of length polynomial in the input length. *)
Definition MachinePolyBounded {L : Language} (P : MachineProofSystem L) : Prop :=
  exists q : Polynomial, forall x, L x = true ->
    exists pi t, length pi <= evalPoly q (length x) /\ verifierRun (verifier P) x pi t true.

(** Verifier runs are deterministic. *)
Theorem verifierRun_deterministic : forall v x pi t t' b b',
  verifierRun v x pi t b -> verifierRun v x pi t' b' -> t = t' /\ b = b'.
Proof.
  intros [m | m] x pi t t' b b' h h'; simpl in h, h'; exact (run_deterministic _ _ _ _ _ _ h h').
Qed.

(** A polynomially bounded machine proof system puts L in NP (proved: the
    proof bound is the certificate bound, and the clock plus determinism bound
    the accepting run). *)
Theorem inNP_of_polyBounded : forall L (P : MachineProofSystem L),
  MachinePolyBounded P -> InNP L.
Proof.
  intros L P [q hq].
  unshelve eexists {| np_language := L; np_verifier := verifier P;
                      np_timeBound := timeBound P; np_certBound := q |}; [| | reflexivity].
  - intros x pi _. exact (halts P x pi).
  - intro x. split.
    + intro hx. destruct (hq x hx) as [pi [t [hlen hr]]].
      destruct (halts P x pi) as [t' [b' [ht' hr']]].
      destruct (verifierRun_deterministic _ _ _ _ _ _ _ hr hr') as [-> _].
      exists pi, t'. split; [exact hlen | split; [exact ht' | exact hr]].
    + intros [pi [t [_ [_ hr]]]]. exact (mps_sound P x pi t hr).
Qed.

(** Every language in P has a polynomially bounded proof system (proved: the
    decider ignores the proof; the empty proof suffices). *)
Theorem proofSystem_of_inP : forall L, InP L ->
  exists P : MachineProofSystem L, MachinePolyBounded P.
Proof.
  intros L h. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  unshelve eexists {| verifier := ignoreCertificate m; timeBound := p |}.
  - intros x pi. destruct (hm x) as [t [b [ht [hr _]]]]. exists t, b. auto.
  - intros x pi t hr. simpl in hr. destruct (hm x) as [t' [b' [_ [hr' hb']]]].
    destruct (run_deterministic _ _ _ _ _ _ hr hr') as [_ <-]. auto.
  - intros x hx. destruct (hm x) as [t [b [_ [hr hb]]]].
    rewrite hx in hb. subst b. exists [], t. exact hr.
  - exists {| coefficient := 0; degree := 0 |}. intros x hx.
    destruct (hm x) as [t [b [_ [hr hb]]]].
    rewrite hx in hb. subst b. exists [], t. split; [simpl; lia | exact hr].
Qed.

(** L has no polynomially bounded machine proof system. *)
Definition NoPolyBoundedMachineProofSystem (L : Language) : Prop :=
  forall P : MachineProofSystem L, ~ MachinePolyBounded P.

(** Open obligation (Cook's program).  UNSAT (complement SAT, over the CNF
    encoding of the shared layer) has no polynomially bounded proof system
    whose verifier is a polynomial-time machine.  With the known theorems
    CookReckhowNP and NPClosedUnderReductions and the Cook-Levin halves, this
    is equivalent to NP <> coNP (noPolyBounded_iff_npNeCoNP). *)
Definition NoPolyBoundedUNSATProofSystem : Prop :=
  NoPolyBoundedMachineProofSystem (complement SAT).

(** A language in P has a polynomially bounded system, so the property is not
    vacuously true. *)
Theorem not_noPolyBounded_of_inP : forall L, InP L -> ~ NoPolyBoundedMachineProofSystem L.
Proof.
  intros L h hno. destruct (proofSystem_of_inP L h) as [P hP]. exact (hno P hP).
Qed.

(** A language outside NP has no polynomially bounded system. *)
Theorem noPolyBounded_of_not_inNP : forall L, ~ InNP L -> NoPolyBoundedMachineProofSystem L.
Proof. intros L h P hP. exact (h (inNP_of_polyBounded L P hP)). Qed.

(** Injective encoding of verifier programs. *)
Definition encVerifier (v : VerifierProgram) : Word :=
  match v with
  | ignoreCertificate m => false :: encMachine m
  | paired m => true :: encMachine m
  end.

Theorem encVerifier_injective : forall v w, encVerifier v = encVerifier w -> v = w.
Proof.
  intros [m | m] [m' | m'] h; simpl in h; injection h; intros; try discriminate;
    f_equal; apply encMachine_injective; assumption.
Qed.

(** Computable decoder for verifier programs, from the front of a word. *)
Definition decVerifierFront (w : Word) : option (VerifierProgram * Word) :=
  match w with
  | false :: r => obind (decMachineFront r) (fun '(m, r') => Some (ignoreCertificate m, r'))
  | true :: r => obind (decMachineFront r) (fun '(m, r') => Some (paired m, r'))
  | [] => None
  end.

Lemma decVerifierFront_encVerifier : forall v r,
  decVerifierFront (encVerifier v ++ r) = Some (v, r).
Proof. intros [m | m] r; simpl; rewrite decMachineFront_encMachine; reflexivity. Qed.

(** Codes of triples (verifier, clock, proof-length bound) and their
    decoder. *)
Definition encVerifierBounds (x : VerifierProgram * Polynomial * Polynomial) : Word :=
  match x with
  | (v, p, q) => encVerifier v ++ encNat (coefficient p) ++ encNat (degree p) ++
                 encNat (coefficient q) ++ encNat (degree q)
  end.

Definition decVerifierBounds (w : Word) : option (VerifierProgram * Polynomial * Polynomial) :=
  obind (decVerifierFront w) (fun '(v, r1) =>
  obind (decNat r1) (fun '(c, r2) =>
  obind (decNat r2) (fun '(k, r3) =>
  obind (decNat r3) (fun '(c', r4) =>
  obind (decNat r4) (fun '(k', _) =>
  Some (v, {| coefficient := c; degree := k |}, {| coefficient := c'; degree := k' |})))))).

Lemma decVerifierBounds_encVerifierBounds : forall x,
  decVerifierBounds (encVerifierBounds x) = Some x.
Proof.
  intros [[v [c k]] [c' k']]. unfold decVerifierBounds, encVerifierBounds. simpl.
  rewrite decVerifierFront_encVerifier. simpl.
  rewrite decNat_encNat. simpl. rewrite decNat_encNat. simpl.
  rewrite decNat_encNat. simpl.
  rewrite <- (app_nil_r (encNat k')), decNat_encNat. reflexivity.
Qed.

(** All words of length at most n. *)
Definition wordsUpTo (n : nat) : list Word := flat_map allAssignments (seq 0 (S n)).

Lemma mem_wordsUpTo : forall n (w : Word), length w <= n -> In w (wordsUpTo n).
Proof.
  intros n w h. unfold wordsUpTo. apply in_flat_map. exists (length w).
  split; [apply in_seq; lia | apply mem_allAssignments_iff; reflexivity].
Qed.

(** The verifier run with the step-bounded interpreter. *)
Definition verifierRunFor (v : VerifierProgram) (x pi : Word) (fuel : nat) : option bool :=
  match v with
  | ignoreCertificate m => runFor m (initial x) fuel
  | paired m => runFor m (pairedInput x pi) fuel
  end.

Lemma verifierRunFor_of_run : forall v x pi t b, verifierRun v x pi t b ->
  forall fuel, t <= fuel -> verifierRunFor v x pi fuel = Some b.
Proof. intros [m | m] x pi t b h fuel hf; exact (runFor_of_run _ _ _ _ h _ hf). Qed.

Lemma run_of_verifierRunFor : forall v x pi fuel b, verifierRunFor v x pi fuel = Some b ->
  exists t, t <= fuel /\ verifierRun v x pi t b.
Proof. intros [m | m] x pi fuel b h; exact (run_of_runFor _ _ _ _ h). Qed.

(** The language of the verifier v as seen with clock p and proof bound q
    (computable; Lean's verifierLanguage is the unbounded classical one):
    some proof of length at most q(|x|) is accepted within the clock. *)
Definition verifierLanguage (v : VerifierProgram) (p q : Polynomial) : Language := fun x =>
  existsb (fun pi => match verifierRunFor v x pi (timeLimit v p x pi) with
                     | Some true => true | _ => false end)
          (wordsUpTo (evalPoly q (length x))).

(** A proof system with proof bound q determines its language (pointwise). *)
Theorem verifierLanguage_eq : forall L (P : MachineProofSystem L) (q : Polynomial),
  (forall x, L x = true -> exists pi t, length pi <= evalPoly q (length x) /\
     verifierRun (verifier P) x pi t true) ->
  forall x, verifierLanguage (verifier P) (timeBound P) q x = L x.
Proof.
  intros L P q hq x. unfold verifierLanguage. destruct (L x) eqn:hx.
  - destruct (hq x hx) as [pi [t [hlen hr]]].
    destruct (halts P x pi) as [t' [b' [ht' hr']]].
    destruct (verifierRun_deterministic _ _ _ _ _ _ _ hr hr') as [<- <-].
    apply existsb_exists. exists pi. split; [apply mem_wordsUpTo; exact hlen |].
    rewrite (verifierRunFor_of_run _ _ _ _ _ hr _ ht'). reflexivity.
  - destruct (existsb _ _) eqn:he; [| reflexivity].
    apply existsb_exists in he. destruct he as [pi [_ hpi]].
    destruct (verifierRunFor (verifier P) x pi _) as [[|] |] eqn:hrun; try discriminate.
    destruct (run_of_verifierRunFor _ _ _ _ _ hrun) as [t [_ hr]].
    rewrite (mps_sound P x pi t hr) in hx. discriminate.
Qed.

(** The diagonal language against all triples (verifier, clock, proof
    bound). *)
Definition noProofSystemLanguage : Language := fun w =>
  match decVerifierBounds w with
  | Some (v, p, q) => negb (verifierLanguage v p q w)
  | None => true
  end.

(** Non-vacuity.  Some language has no polynomially bounded machine proof
    system (direct pointwise diagonal). *)
Theorem exists_noPolyBounded : exists L : Language, NoPolyBoundedMachineProofSystem L.
Proof.
  exists noProofSystemLanguage. intros P [q hq].
  set (w := encVerifierBounds (verifier P, timeBound P, q)).
  pose proof (verifierLanguage_eq _ P q hq w) as he.
  assert (hd : noProofSystemLanguage w = negb (verifierLanguage (verifier P) (timeBound P) q w)).
  { unfold noProofSystemLanguage, w. rewrite decVerifierBounds_encVerifierBounds. reflexivity. }
  rewrite he in hd. destruct (noProofSystemLanguage w); discriminate.
Qed.

(** Conditional theorem (proved).  The obligation gives ~ InP SAT
    unconditionally. *)
Theorem not_inP_sat_of_noPolyBounded : NoPolyBoundedUNSATProofSystem -> ~ InP SAT.
Proof. intros h hs. exact (not_noPolyBounded_of_inP _ (inP_complement _ hs) h). Qed.

(** Conditional theorem (proved).  With SAT in NP (one half of Cook-Levin, a
    named hypothesis) the obligation gives P <> NP. *)
Theorem pNotEqualsNP_of_noPolyBounded : SATInNP -> NoPolyBoundedUNSATProofSystem ->
  PNotEqualsNP.
Proof.
  intros mem h hp. exact (not_inP_sat_of_noPolyBounded h (inP_sat_of_pEqualsNP mem hp)).
Qed.

(** Known theorem, not mechanised here: every NP language has a polynomially
    bounded machine proof system (Cook and Reckhow, J. Symbolic Logic 44(1),
    1979).  The converse direction is proved (inNP_of_polyBounded). *)
Definition CookReckhowNP : Prop :=
  forall L : Language, InNP L -> exists P : MachineProofSystem L, MachinePolyBounded P.

(** Known theorem, not mechanised here: NP is closed under polynomial-time
    many-one reductions (Karp 1972). *)
Definition NPClosedUnderReductions : Prop :=
  forall L L' : Language, PolyReduces L L' -> InNP L' -> InNP L.

(** A reduction from L to L' is also one from the complements. *)
Theorem polyReduces_complement : forall L L', PolyReduces L L' ->
  PolyReduces (complement L) (complement L').
Proof.
  intros L L' [m [f [p [hc hf]]]]. exists m, f, p. split; [exact hc |].
  intro x. unfold complement. rewrite hf. reflexivity.
Qed.

(** Conditional theorem (proved).  The obligation gives NP <> coNP, given
    SAT in NP and CookReckhowNP. *)
Theorem npNeCoNP_of_noPolyBounded : SATInNP -> CookReckhowNP ->
  NoPolyBoundedUNSATProofSystem -> ~ NPEqualsCoNP.
Proof.
  intros mem hcr h heq. destruct (hcr _ (proj1 (heq SAT) mem)) as [P hP]. exact (h P hP).
Qed.

Theorem pNotEqualsNP_via_coNP : SATInNP -> CookReckhowNP ->
  NoPolyBoundedUNSATProofSystem -> PNotEqualsNP.
Proof.
  intros mem hcr h. apply pNotEqualsNP_of_npNeCoNP. exact (npNeCoNP_of_noPolyBounded mem hcr h).
Qed.

(** Converse (proved from named hypotheses).  A polynomially bounded system
    for UNSAT gives NP = coNP, given SAT's NP-hardness and closure of NP under
    reductions. *)
Theorem npEqualsCoNP_of_polyBounded : SATHard -> NPClosedUnderReductions ->
  forall P : MachineProofSystem (complement SAT), MachinePolyBounded P -> NPEqualsCoNP.
Proof.
  intros hard hclosed P hP.
  pose proof (inNP_of_polyBounded _ P hP) as hu.
  intro L. split.
  - intro hL. exact (hclosed _ _ (polyReduces_complement _ _ (hard L hL)) hu).
  - intro hL.
    destruct (polyReduces_complement _ _ (hard _ hL)) as [m [f [p [hc hf]]]].
    apply (hclosed L (complement SAT)); [| exact hu].
    exists m, f, p. split; [exact hc |].
    intro x. rewrite <- hf. symmetry. apply complement_complement.
Qed.

(** Cook-Reckhow equivalence (proved from named hypotheses). *)
Theorem noPolyBounded_iff_npNeCoNP : SATInNP -> SATHard -> CookReckhowNP ->
  NPClosedUnderReductions -> (NoPolyBoundedUNSATProofSystem <-> ~ NPEqualsCoNP).
Proof.
  intros mem hard hcr hclosed. split.
  - exact (npNeCoNP_of_noPolyBounded mem hcr).
  - intros hne P hP. exact (hne (npEqualsCoNP_of_polyBounded hard hclosed P hP)).
Qed.
