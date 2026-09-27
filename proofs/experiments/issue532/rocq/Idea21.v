(* Issue #532, Idea 21: exact SAT by branching (DPLL splitting).

   Rocq counterpart of lean/Idea21.lean.  Proves for every CNF: restriction
   is evaluation under the updated assignment (eval_restrict); the splitting
   rule sat_split; correctness of pure splitting (solve_correct) and of
   DPLL-style splitting with pruning (dpll_correct) for every CNF whose
   variables lie in the branching list; the unpruned tree has exactly
   2^|vs| leaves (leaves_eq) and the pruned tree at most that many
   (dpllLeaves_le).  Verdict: correct but exponential; exponential lower
   bounds for DPLL/CDCL on explicit families follow from published
   resolution lower bounds (Haken 1985 and others), cited, not formalized.
   The Lean version tests "phi = []" and "[] in phi" with decidable
   propositions; here the Boolean tests isNil and existsb isEmptyClause are
   used. *)

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

(* ---------- Splitting solvers ---------- *)

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

Fixpoint leaves (vs : list nat) (phi : CNF) : nat :=
  match vs with
  | [] => 1
  | v :: vs' => leaves vs' (restrict v true phi) + leaves vs' (restrict v false phi)
  end.

Theorem leaves_eq : forall vs phi, leaves vs phi = 2 ^ length vs.
Proof.
  induction vs as [|v vs IH]; intros phi; [reflexivity|].
  cbn [leaves length]. rewrite !IH. rewrite Nat.pow_succ_r'. lia.
Qed.

Theorem empty_clause_unsat : forall phi, In [] phi -> ~ Satisfiable phi.
Proof.
  intros phi Hin [a Ha]. rewrite evalCNF_true_iff in Ha.
  specialize (Ha [] Hin). discriminate.
Qed.

Definition isNil (phi : CNF) : bool :=
  match phi with [] => true | _ => false end.

Definition isEmptyClause (C : Clause) : bool :=
  match C with [] => true | _ => false end.

Lemma existsb_isEmpty : forall phi, existsb isEmptyClause phi = true <-> In [] phi.
Proof.
  intros phi. rewrite existsb_exists. split.
  - intros [C [HC HE]]. destruct C; [exact HC | discriminate].
  - intros H. exists []. split; auto.
Qed.

Fixpoint dpll (vs : list nat) (phi : CNF) : bool :=
  match vs with
  | [] => evalCNF (fun _ => false) phi
  | v :: vs' =>
      if isNil phi then true
      else if existsb isEmptyClause phi then false
      else dpll vs' (restrict v true phi) || dpll vs' (restrict v false phi)
  end.

Theorem dpll_correct : forall vs phi, VarsIn phi vs ->
  (dpll vs phi = true <-> Satisfiable phi).
Proof.
  induction vs as [|v vs IH]; intros phi H.
  - cbn [dpll]. rewrite sat_no_vars by exact H. reflexivity.
  - cbn [dpll]. destruct (isNil phi) eqn:E0.
    + destruct phi; [|discriminate]. split; [|reflexivity].
      intros _. exists (fun _ => false). reflexivity.
    + destruct (existsb isEmptyClause phi) eqn:E1.
      * apply existsb_isEmpty in E1. split; [discriminate|].
        intros Hs. exfalso. exact (empty_clause_unsat phi E1 Hs).
      * rewrite sat_split with (v := v), orb_true_iff.
        rewrite (IH _ (restrict_vars phi v vs true H)), (IH _ (restrict_vars phi v vs false H)).
        reflexivity.
Qed.

Fixpoint dpllLeaves (vs : list nat) (phi : CNF) : nat :=
  match vs with
  | [] => 1
  | v :: vs' =>
      if isNil phi then 1
      else if existsb isEmptyClause phi then 1
      else dpllLeaves vs' (restrict v true phi) + dpllLeaves vs' (restrict v false phi)
  end.

Theorem dpllLeaves_le : forall vs phi, dpllLeaves vs phi <= 2 ^ length vs.
Proof.
  induction vs as [|v vs IH]; intros phi; [cbn; lia|].
  cbn [dpllLeaves length]. rewrite Nat.pow_succ_r'.
  assert (Hpos : 1 <= 2 ^ length vs).
  { pose proof (Nat.pow_nonzero 2 (length vs) ltac:(lia)). lia. }
  destruct (isNil phi); [lia|].
  destruct (existsb isEmptyClause phi); [lia|].
  pose proof (IH (restrict v true phi)). pose proof (IH (restrict v false phi)). lia.
Qed.
