(* Issue #532, Idea 24: unit propagation.

   Proved, for every CNF: a unit clause forces its literal (unit_forces);
   propagating a true literal does not change the value of the formula
   (propagate_preserves); fuel-bounded unit propagation preserves
   satisfiability (up_equisat), so a derived empty clause certifies UNSAT
   (up_conflict_unsat); for every CNF psi with clauses of length >= 2 and all
   x y, the formula sq x y ++ psi is unsatisfiable yet left unchanged by
   propagation (up_incomplete_family); on Horn formulas positive unit
   propagation followed by the all-false assignment decides satisfiability
   (hornSolve_correct).

   Verdict: Correct tool, insufficient alone (general theorem proved). *)

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


(* ---------- Unit propagation: soundness ---------- *)

Lemma evalLit_true_iff : forall a l, evalLit a l = true <-> a (var l) = pos l.
Proof.
  intros a [v p]. unfold evalLit. cbn [var pos].
  destruct p, (a v); split; intros H; try reflexivity; discriminate.
Qed.

(* A unit clause forces its literal. *)
Theorem unit_forces : forall a phi l, In [l] phi -> evalCNF a phi = true ->
  evalLit a l = true.
Proof.
  intros a phi l Hin Ha.
  pose proof (proj1 (evalCNF_true_iff a phi) Ha [l] Hin) as H.
  cbn [evalClause] in H. rewrite orb_false_r in H. exact H.
Qed.

(* Propagation preserves satisfying assignments. *)
Theorem propagate_preserves : forall a phi l, evalLit a l = true ->
  evalCNF a (restrict (var l) (pos l) phi) = evalCNF a phi.
Proof.
  intros a phi l H. apply evalLit_true_iff in H.
  rewrite eval_restrict, <- H. apply eval_congr.
  intros C l' _ _. apply setVar_self.
Qed.

(* One propagation step preserves satisfiability. *)
Theorem unit_step_equisat : forall l phi, In [l] phi ->
  (Satisfiable (restrict (var l) (pos l) phi) <-> Satisfiable phi).
Proof.
  intros l phi Hin. split.
  - intros [a Ha]. exists (setVar a (var l) (pos l)). rewrite <- eval_restrict. exact Ha.
  - intros [a Ha]. exists a.
    rewrite (propagate_preserves a phi l (unit_forces a phi l Hin Ha)). exact Ha.
Qed.

Definition unitOf (C : Clause) : option Lit :=
  match C with
  | [l] => Some l
  | _ => None
  end.

Fixpoint findUnit (phi : CNF) : option Lit :=
  match phi with
  | [] => None
  | C :: phi' => match unitOf C with
                 | Some l => Some l
                 | None => findUnit phi'
                 end
  end.

Lemma unitOf_some : forall C l, unitOf C = Some l -> C = [l].
Proof.
  intros [|l1 [|l2 C]] l H; cbn in H; try discriminate.
  injection H as E. subst. reflexivity.
Qed.

Lemma findUnit_some : forall phi l, findUnit phi = Some l -> In [l] phi.
Proof.
  induction phi as [|C phi IH]; intros l H; cbn in H; [discriminate|].
  destruct (unitOf C) as [l'|] eqn:E.
  - injection H as H. subst. left. apply unitOf_some. exact E.
  - right. apply IH. exact H.
Qed.

Lemma unitOf_long : forall C, 2 <= length C -> unitOf C = None.
Proof.
  intros [|l1 [|l2 C]] H; cbn in H; try lia. reflexivity.
Qed.

Lemma findUnit_none_of_long : forall phi,
  (forall C, In C phi -> 2 <= length C) -> findUnit phi = None.
Proof.
  induction phi as [|C phi IH]; intros H; [reflexivity|].
  cbn [findUnit]. rewrite (unitOf_long C (H C (or_introl eq_refl))).
  apply IH. intros C' HC'. apply H. right. exact HC'.
Qed.

(* Unit propagation with fuel. *)
Fixpoint up (n : nat) (phi : CNF) : CNF :=
  match n with
  | 0 => phi
  | S n' => match findUnit phi with
            | None => phi
            | Some l => up n' (restrict (var l) (pos l) phi)
            end
  end.

(* Soundness of unit propagation. *)
Theorem up_equisat : forall n phi, Satisfiable (up n phi) <-> Satisfiable phi.
Proof.
  induction n as [|n IH]; intros phi; [reflexivity|].
  cbn [up]. destruct (findUnit phi) as [l|] eqn:E; [|reflexivity].
  rewrite IH. apply unit_step_equisat. apply findUnit_some. exact E.
Qed.

Theorem empty_clause_unsat : forall phi, In [] phi -> ~ Satisfiable phi.
Proof.
  intros phi Hin [a Ha].
  pose proof (proj1 (evalCNF_true_iff a phi) Ha [] Hin) as H. discriminate H.
Qed.

(* A conflict found by propagation certifies unsatisfiability. *)
Theorem up_conflict_unsat : forall n phi, In [] (up n phi) -> ~ Satisfiable phi.
Proof.
  intros n phi H Hs. apply (empty_clause_unsat _ H). apply up_equisat. exact Hs.
Qed.

(* ---------- Incompleteness ---------- *)

Theorem up_noop : forall n phi, (forall C, In C phi -> 2 <= length C) -> up n phi = phi.
Proof.
  intros [|n] phi H; [reflexivity|].
  cbn [up]. rewrite (findUnit_none_of_long phi H). reflexivity.
Qed.

Definition sq (x y : nat) : CNF :=
  [[mkLit x true; mkLit y true]; [mkLit x true; mkLit y false];
   [mkLit x false; mkLit y true]; [mkLit x false; mkLit y false]].

Theorem sq_unsat : forall x y, ~ Satisfiable (sq x y).
Proof.
  intros x y [a Ha]. unfold sq in Ha. cbn in Ha.
  destruct (a x), (a y); discriminate Ha.
Qed.

Lemma sq_long : forall x y C, In C (sq x y) -> 2 <= length C.
Proof.
  intros x y C H. unfold sq in H.
  destruct H as [E|[E|[E|[E|[]]]]]; subst; cbn; lia.
Qed.

(* Incompleteness of unit propagation (general family). *)
Theorem up_incomplete_family : forall psi,
  (forall C, In C psi -> 2 <= length C) -> forall x y n,
  up n (sq x y ++ psi) = sq x y ++ psi /\ ~ In [] (up n (sq x y ++ psi)) /\
  ~ Satisfiable (sq x y ++ psi).
Proof.
  intros psi Hpsi x y n.
  assert (Hl : forall C, In C (sq x y ++ psi) -> 2 <= length C).
  { intros C HC. apply in_app_or in HC. destruct HC as [HC|HC].
    - exact (sq_long x y C HC).
    - exact (Hpsi C HC). }
  split; [|split].
  - apply up_noop. exact Hl.
  - rewrite (up_noop n _ Hl). intros H. pose proof (Hl [] H) as H'. cbn in H'. lia.
  - intros [a Ha]. apply (sq_unsat x y). exists a.
    apply evalCNF_true_iff. intros C HC.
    apply (proj1 (evalCNF_true_iff a _) Ha). apply in_or_app. left. exact HC.
Qed.

(* ---------- Horn formulas ---------- *)

Fixpoint posCount (C : Clause) : nat :=
  match C with
  | [] => 0
  | l :: C' => (if pos l then 1 else 0) + posCount C'
  end.

Definition IsHorn (phi : CNF) : Prop := forall C, In C phi -> posCount C <= 1.

Lemma posCount_removeVar_le : forall v C, posCount (removeVar v C) <= posCount C.
Proof.
  intros v C. induction C as [|l C IH]; cbn [removeVar posCount]; [lia|].
  destruct (Nat.eqb (var l) v); cbn [posCount]; lia.
Qed.

(* Restriction preserves the Horn property. *)
Theorem restrict_horn : forall v b phi, IsHorn phi -> IsHorn (restrict v b phi).
Proof.
  intros v b phi H C' HC'.
  destruct (mem_restrict v b phi C' HC') as [C [HC E]]. subst C'.
  pose proof (posCount_removeVar_le v C). pose proof (H C HC). lia.
Qed.

Fixpoint hasEmpty (phi : CNF) : bool :=
  match phi with
  | [] => false
  | [] :: _ => true
  | (_ :: _) :: phi' => hasEmpty phi'
  end.

Lemma hasEmpty_iff : forall phi, hasEmpty phi = true <-> In [] phi.
Proof.
  induction phi as [|C phi IH]; cbn.
  - split; [discriminate | intros []].
  - destruct C as [|l C].
    + split; [intros _; left; reflexivity | reflexivity].
    + rewrite IH. split; [intros H; right; exact H|].
      intros [H|H]; [discriminate | exact H].
Qed.

Definition posUnitOf (C : Clause) : option nat :=
  match C with
  | [l] => if pos l then Some (var l) else None
  | _ => None
  end.

Fixpoint findPosUnit (phi : CNF) : option nat :=
  match phi with
  | [] => None
  | C :: phi' => match posUnitOf C with
                 | Some v => Some v
                 | None => findPosUnit phi'
                 end
  end.

Lemma posUnitOf_some : forall C v, posUnitOf C = Some v -> C = [mkLit v true].
Proof.
  intros [|[lv lp] [|l2 C]] v H; cbn in H; try discriminate.
  destruct lp; [|discriminate]. injection H as E. subst. reflexivity.
Qed.

Lemma findPosUnit_some : forall phi v, findPosUnit phi = Some v -> In [mkLit v true] phi.
Proof.
  induction phi as [|C phi IH]; intros v H; cbn in H; [discriminate|].
  destruct (posUnitOf C) as [w|] eqn:E.
  - injection H as H. subst. left. apply posUnitOf_some. exact E.
  - right. apply IH. exact H.
Qed.

Lemma findPosUnit_none : forall phi, findPosUnit phi = None ->
  forall C, In C phi -> posUnitOf C = None.
Proof.
  induction phi as [|D phi IH]; intros H C HC; [destruct HC|].
  cbn in H. destruct (posUnitOf D) eqn:E; [discriminate|].
  destruct HC as [HC|HC]; [subst; exact E | exact (IH H C HC)].
Qed.

Lemma neg_or_allpos : forall C,
  (exists l, In l C /\ pos l = false) \/ posCount C = length C.
Proof.
  induction C as [|l C IH]; [right; reflexivity|].
  destruct (pos l) eqn:Hp.
  - destruct IH as [[l' [Hl' E]]|E].
    + left. exists l'. split; [right|]; assumption.
    + right. cbn [posCount length]. rewrite Hp, E. reflexivity.
  - left. exists l. split; [left; reflexivity | exact Hp].
Qed.

(* A nonempty Horn clause that is not a positive unit is satisfied by the
   all-false assignment. *)
Lemma horn_clause_sat : forall C, posCount C <= 1 -> C <> [] -> posUnitOf C = None ->
  evalClause (fun _ => false) C = true.
Proof.
  intros C Hh Hne Hu.
  destruct (neg_or_allpos C) as [[l [Hl Hp]]|E].
  - apply evalClause_true_iff. exists l. split; [exact Hl|].
    unfold evalLit. rewrite Hp. reflexivity.
  - destruct C as [|l [|l2 C]]; [contradiction Hne; reflexivity| |].
    + cbn in Hu, E. destruct (pos l); [discriminate | cbn in E; lia].
    + cbn [length] in E. lia.
Qed.

(* Horn fixpoint lemma. *)
Theorem horn_fixpoint_sat : forall phi, IsHorn phi -> hasEmpty phi = false ->
  findPosUnit phi = None -> evalCNF (fun _ => false) phi = true.
Proof.
  intros phi Hh He Hu. apply evalCNF_true_iff. intros C HC.
  apply horn_clause_sat; [exact (Hh C HC) | | exact (findPosUnit_none phi Hu C HC)].
  intros E. subst C. apply hasEmpty_iff in HC. congruence.
Qed.

(* Propagating a unit clause strictly decreases the size. *)
Lemma size_restrict_lt : forall phi l, In [l] phi ->
  size (restrict (var l) (pos l) phi) < size phi.
Proof.
  intros phi l.
  assert (Hself : clauseHas (var l) (pos l) [l] = true).
  { cbn. rewrite Nat.eqb_refl, eqb_reflx. reflexivity. }
  induction phi as [|C phi IH]; intros H; [destruct H|].
  destruct H as [E|E].
  - subst C. cbn [restrict]. rewrite Hself. cbn [size length].
    pose proof (size_restrict_le (var l) (pos l) phi). lia.
  - pose proof (IH E). pose proof (length_removeVar_le (var l) C).
    cbn [restrict]. destruct (clauseHas (var l) (pos l) C); cbn [size]; lia.
Qed.

Fixpoint hornUP (n : nat) (phi : CNF) : bool :=
  match n with
  | 0 => evalCNF (fun _ => false) phi
  | S n' => if hasEmpty phi then false else
             match findPosUnit phi with
             | None => true
             | Some v => hornUP n' (restrict v true phi)
             end
  end.

Theorem hornUP_correct : forall n phi, IsHorn phi -> size phi <= n ->
  (hornUP n phi = true <-> Satisfiable phi).
Proof.
  induction n as [|n IH]; intros phi Hh Hs.
  - destruct phi as [|C phi]; [|cbn in Hs; lia].
    cbn. split; [intros _; exists (fun _ => false); reflexivity | reflexivity].
  - cbn [hornUP]. destruct (hasEmpty phi) eqn:He.
    + split; [discriminate|]. intros Hsat.
      exfalso. exact (empty_clause_unsat phi (proj1 (hasEmpty_iff phi) He) Hsat).
    + destruct (findPosUnit phi) as [v|] eqn:Hu.
      * pose proof (findPosUnit_some phi v Hu) as Hmem.
        pose proof (size_restrict_lt phi (mkLit v true) Hmem) as Hlt. cbn [var pos] in Hlt.
        rewrite (IH _ (restrict_horn v true phi Hh)) by lia.
        exact (unit_step_equisat (mkLit v true) phi Hmem).
      * split; [|reflexivity]. intros _.
        exists (fun _ => false). exact (horn_fixpoint_sat phi Hh He Hu).
Qed.

Definition hornSolve (phi : CNF) : bool := hornUP (size phi) phi.

(* Horn-SAT is decided by unit propagation. *)
Theorem hornSolve_correct : forall phi, IsHorn phi ->
  (hornSolve phi = true <-> Satisfiable phi).
Proof.
  intros phi Hh. exact (hornUP_correct (size phi) phi Hh (le_n _)).
Qed.
