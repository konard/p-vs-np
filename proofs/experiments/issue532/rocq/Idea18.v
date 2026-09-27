(* Issue #532, Idea 18: structural restrictions and easy subclasses of SAT.

   Rocq counterpart of lean/Idea18.lean.  General theorems: 1-valid / 0-valid
   CNFs are satisfied by the all-true / all-false assignment; unit CNFs are
   satisfiable iff they have no empty clause and no complementary unit pair
   (with a correct Boolean decider); no satisfiability-preserving map of any
   kind lands in a trivially satisfiable class; and a polynomial-size
   reduction into a decidable restricted class transfers correctness and a
   composed polynomial cost bound.  The hypothesis PolySizeReductionInto is
   the open obligation and is only defined. *)

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

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | C :: phi' => length C + 1 + size phi'
  end.

(* ---------- (a) 1-valid and 0-valid classes ---------- *)

Definition PositiveClauses (phi : CNF) : Prop :=
  forall C, In C phi -> exists l, In l C /\ pos l = true.

Definition NegativeClauses (phi : CNF) : Prop :=
  forall C, In C phi -> exists l, In l C /\ pos l = false.

Theorem allTrue_satisfies : forall phi,
  PositiveClauses phi -> evalCNF (fun _ => true) phi = true.
Proof.
  intros phi H. apply evalCNF_true_iff. intros C HC.
  destruct (H C HC) as [l [Hl Hp]]. apply evalClause_true_iff.
  exists l. split; auto. unfold evalLit. rewrite Hp. reflexivity.
Qed.

Theorem allFalse_satisfies : forall phi,
  NegativeClauses phi -> evalCNF (fun _ => false) phi = true.
Proof.
  intros phi H. apply evalCNF_true_iff. intros C HC.
  destruct (H C HC) as [l [Hl Hp]]. apply evalClause_true_iff.
  exists l. split; auto. unfold evalLit. rewrite Hp. reflexivity.
Qed.

Theorem positive_satisfiable : forall phi, PositiveClauses phi -> Satisfiable phi.
Proof. intros phi H. exists (fun _ => true). apply allTrue_satisfies; auto. Qed.

Theorem negative_satisfiable : forall phi, NegativeClauses phi -> Satisfiable phi.
Proof. intros phi H. exists (fun _ => false). apply allFalse_satisfies; auto. Qed.

(* ---------- (b) Unit CNFs ---------- *)

Definition IsUnitCNF (phi : CNF) : Prop := forall C, In C phi -> length C <= 1.

Definition UnitClash (phi : CNF) : Prop :=
  exists l1 l2, In [l1] phi /\ In [l2] phi /\ var l1 = var l2 /\ pos l1 <> pos l2.

Lemma clause_of_length_le_one : forall C : Clause,
  length C <= 1 -> C <> [] -> exists l, C = [l].
Proof.
  intros [|l [|l' C]] H Hne; simpl in *.
  - contradiction.
  - exists l. reflexivity.
  - lia.
Qed.

Theorem unitCNF_sat_iff : forall phi, IsUnitCNF phi ->
  (Satisfiable phi <-> (~ In [] phi /\ ~ UnitClash phi)).
Proof.
  intros phi Hu. split.
  - intros [a Ha]. rewrite evalCNF_true_iff in Ha. split.
    + intros Hin. specialize (Ha [] Hin). discriminate.
    + intros [l1 [l2 [H1 [H2 [Hv Hp]]]]].
      pose proof (Ha _ H1) as E1. pose proof (Ha _ H2) as E2.
      simpl in E1, E2. rewrite orb_false_r in E1, E2.
      unfold evalLit in E1, E2. rewrite Hv in E1.
      destruct (pos l1), (pos l2); try (apply Hp; reflexivity);
        destruct (a (var l2)); discriminate.
  - intros [Hne Hclash].
    exists (fun v => if in_dec clause_eq_dec [mkLit v true] phi then true else false).
    apply evalCNF_true_iff. intros C HC.
    assert (HCne : C <> []) by (intros E; subst; contradiction).
    destruct (clause_of_length_le_one C (Hu C HC) HCne) as [l E]. subst C.
    simpl. rewrite orb_false_r. unfold evalLit.
    destruct l as [v p]; simpl. destruct p.
    + destruct (in_dec clause_eq_dec [mkLit v true] phi) as [H|H]; auto.
    + destruct (in_dec clause_eq_dec [mkLit v true] phi) as [H|H]; auto.
      exfalso. apply Hclash. exists (mkLit v true), (mkLit v false).
      repeat split; auto. simpl. discriminate.
Qed.

Definition isEmptyClause (C : Clause) : bool :=
  match C with [] => true | _ => false end.

Definition unitDecide (phi : CNF) : bool :=
  negb (existsb isEmptyClause phi) &&
  forallb (fun C1 => forallb (fun C2 =>
    match C1, C2 with
    | [l1], [l2] => negb (Nat.eqb (var l1) (var l2) && negb (Bool.eqb (pos l1) (pos l2)))
    | _, _ => true
    end) phi) phi.

Lemma existsb_isEmpty : forall phi, existsb isEmptyClause phi = true <-> In [] phi.
Proof.
  intros phi. rewrite existsb_exists. split.
  - intros [C [HC HE]]. destruct C; [auto | discriminate].
  - intros H. exists []. auto.
Qed.

Theorem unitDecide_correct : forall phi, IsUnitCNF phi ->
  (unitDecide phi = true <-> Satisfiable phi).
Proof.
  intros phi Hu. rewrite (unitCNF_sat_iff phi Hu). unfold unitDecide.
  rewrite andb_true_iff, negb_true_iff. split.
  - intros [Hne Hall]. split.
    + intros Hin. apply existsb_isEmpty in Hin. congruence.
    + intros [l1 [l2 [H1 [H2 [Hv Hp]]]]].
      rewrite forallb_forall in Hall. specialize (Hall _ H1).
      rewrite forallb_forall in Hall. specialize (Hall _ H2).
      simpl in Hall. rewrite Hv, Nat.eqb_refl in Hall.
      destruct (pos l1), (pos l2); simpl in Hall; try discriminate; apply Hp; reflexivity.
  - intros [Hne Hclash]. split.
    + destruct (existsb isEmptyClause phi) eqn:E; auto.
      apply existsb_isEmpty in E. contradiction.
    + apply forallb_forall. intros C1 H1. apply forallb_forall. intros C2 H2.
      destruct C1 as [|l1 [|l1' C1]]; auto.
      destruct C2 as [|l2 [|l2' C2]]; auto.
      destruct (Nat.eqb (var l1) (var l2)) eqn:Ev; simpl; auto.
      apply Nat.eqb_eq in Ev.
      destruct (Bool.eqb (pos l1) (pos l2)) eqn:Ep; simpl; auto.
      exfalso. apply Hclash. exists l1, l2. repeat split; auto.
      intros Heq. rewrite Heq, eqb_reflx in Ep. discriminate.
Qed.

(* ---------- (c) Reductions into trivial classes ---------- *)

Theorem reduction_into_trivial_class : forall (A B : Type) (L : A -> Prop) (M : B -> Prop)
  (f : A -> B), (forall x, L x <-> M (f x)) -> (forall y, M y) -> forall x, L x.
Proof. intros A B L M f Hred Hc x. apply Hred. apply Hc. Qed.

Theorem no_reduction_of_nontrivial : forall (A B : Type) (L : A -> Prop) (M : B -> Prop),
  (exists x, ~ L x) -> (forall y, M y) -> ~ exists f : A -> B, forall x, L x <-> M (f x).
Proof.
  intros A B L M [x Hx] Hc [f Hf]. apply Hx.
  apply (reduction_into_trivial_class A B L M f Hf Hc).
Qed.

Theorem empty_clause_unsat : ~ Satisfiable [[]].
Proof. intros [a Ha]. discriminate. Qed.

Theorem no_sat_reduction_into_positive :
  ~ exists f : CNF -> CNF, (forall phi, PositiveClauses (f phi)) /\
                           (forall phi, Satisfiable phi <-> Satisfiable (f phi)).
Proof.
  intros [f [Hpos Hpres]]. apply empty_clause_unsat.
  apply Hpres. apply positive_satisfiable. apply Hpos.
Qed.

Theorem no_sat_reduction_into_negative :
  ~ exists f : CNF -> CNF, (forall phi, NegativeClauses (f phi)) /\
                           (forall phi, Satisfiable phi <-> Satisfiable (f phi)).
Proof.
  intros [f [Hneg Hpres]]. apply empty_clause_unsat.
  apply Hpres. apply negative_satisfiable. apply Hneg.
Qed.

(* ---------- The useful direction: hardness-preserving restriction ---------- *)

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

(* Open obligation: SAT reduces into R with polynomial size blow-up.  Only
   defined.  It records the size bound only; without a requirement that the
   map be computable in polynomial time it carries no P vs NP content (the
   Lean file proves the size-only version for unit CNF). *)
Definition PolySizeReductionInto (R : CNF -> Prop) : Prop :=
  exists (f : CNF -> CNF) (c k : nat),
    (forall phi, R (f phi)) /\ (forall phi, Satisfiable phi <-> Satisfiable (f phi)) /\
    (forall phi, size (f phi) <= polyEval c k (size phi)).

Theorem poly_comp_bound : forall c k c' k' n,
  polyEval c' k' (polyEval c k n) <= polyEval (c' * (c + 1) ^ k') (k * k') n.
Proof.
  intros c k c' k' n. unfold polyEval.
  assert (H1 : 1 <= (n + 1) ^ k).
  { pose proof (Nat.pow_le_mono_l 1 (n + 1) k ltac:(lia)). rewrite Nat.pow_1_l in H. lia. }
  assert (H2 : c * (n + 1) ^ k + 1 <= (c + 1) * (n + 1) ^ k) by nia.
  pose proof (Nat.pow_le_mono_l _ _ k' H2) as H3.
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in H3.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. exact H3.
Qed.

Theorem restriction_transfer : forall (R : CNF -> Prop),
  PolySizeReductionInto R ->
  forall (d : CNF -> bool), (forall psi, R psi -> (d psi = true <-> Satisfiable psi)) ->
  forall (dcost : CNF -> nat) (c' k' : nat),
    (forall psi, dcost psi <= polyEval c' k' (size psi)) ->
    exists (f : CNF -> CNF) (C K : nat),
      (forall phi, d (f phi) = true <-> Satisfiable phi) /\
      (forall phi, dcost (f phi) <= polyEval C K (size phi)).
Proof.
  intros R [f [c [k [HfR [Hfsat Hfsize]]]]] d Hd dcost c' k' Hcost.
  exists f, (c' * (c + 1) ^ k'), (k * k'). split.
  - intros phi. rewrite (Hd _ (HfR phi)). symmetry. apply Hfsat.
  - intros phi. eapply Nat.le_trans; [apply Hcost|].
    eapply Nat.le_trans; [|apply poly_comp_bound].
    unfold polyEval. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l.
    specialize (Hfsize phi). unfold polyEval in Hfsize. lia.
Qed.
