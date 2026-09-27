(** * Issue #532, Idea 02 -- Certificate search: the black-box query lower bound

    Rocq counterpart of [lean/Idea02.lean]; theorem names are aligned.

    - [pigeonhole], [exists_unqueried], [nonadaptive_indistinguishable]:
      fewer than 2^n queries miss a length-n vector, and the indicator of that
      vector agrees with the all-false predicate on every query;
    - [no_shallow_decision_tree]: no adaptive decision tree of depth < 2^n
      decides "exists x of length n with f x = true" for all f;
    - [linearTree_decides], [linearTree_depth]: depth 2^n suffices (tight);
    - [pointCNF_iff], [pointCNF_satisfiable]: every vector is the unique
      satisfying length-n vector of n unit clauses;
    - [failed_trials_do_not_certify], [no_shallow_cnf_blackbox]: the same
      bounds for CNFs accessed only through evaluation queries.

    Verdict: refuted as a route for black-box / certificate-trial methods;
    a P = NP algorithm must exploit the formula's structure. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(** ** Enumeration and pigeonhole *)

Fixpoint allAssignments (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allAssignments n') ++ map (cons true) (allAssignments n')
  end.

Theorem length_allAssignments (n : nat) : length (allAssignments n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allAssignments_iff (n : nat) (v : list bool) :
  In v (allAssignments n) <-> length v = n.
Proof.
  revert v; induction n as [|n IH]; intros v.
  - destruct v as [|b v]; simpl; split; intros H; auto; try discriminate.
    destruct H as [H|H]; [discriminate|contradiction].
  - destruct v as [|b v]; simpl; rewrite in_app_iff, !in_map_iff; split.
    + intros [[w [Hw _]]|[w [Hw _]]]; discriminate.
    + intros H; discriminate.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; injection Hw; intros; subst;
        f_equal; apply IH; auto.
    + intros H; injection H; intros H'; destruct b.
      * right; exists v; split; auto; apply IH; auto.
      * left; exists v; split; auto; apply IH; auto.
Qed.

Lemma nodup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 H; simpl; auto.
  inversion H1; subst. constructor.
  - intros Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + contradiction.
    + apply (H x); simpl; auto.
  - apply IH; auto. intros y Hy; apply H; simpl; auto.
Qed.

Lemma nodup_map_cons (b : bool) (L : list (list bool)) :
  NoDup L -> NoDup (map (cons b) L).
Proof.
  induction L as [|x L IH]; intros H; simpl; constructor.
  - inversion H; subst. intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hin]]; injection Hy; intros; subst; contradiction.
  - inversion H; subst; auto.
Qed.

Theorem nodup_allAssignments (n : nat) : NoDup (allAssignments n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; auto | constructor].
  - apply nodup_app_intro; try apply nodup_map_cons; auto.
    intros x Hx Hy; apply in_map_iff in Hx; apply in_map_iff in Hy.
    destruct Hx as [u [Hu _]]; destruct Hy as [w [Hw _]]; subst.
    discriminate.
Qed.

(** Pigeonhole principle for lists (proved by removing one occurrence). *)
Theorem pigeonhole {A : Type} (L Q : list A) :
  NoDup L -> (forall x, In x L -> In x Q) -> length L <= length Q.
Proof.
  revert Q; induction L as [|x L IH]; intros Q HL H; simpl; [lia|].
  inversion HL; subst.
  destruct (in_split x Q (H x (or_introl eq_refl))) as [Q1 [Q2 HQ]]; subst Q.
  assert (Hle : length L <= length (Q1 ++ Q2)).
  { apply IH; auto. intros y Hy.
    assert (Hin : In y (Q1 ++ x :: Q2)) by (apply H; simpl; auto).
    apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin|[Hin|Hin]]; auto.
    subst; contradiction. }
  rewrite length_app in *; simpl; lia.
Qed.

Theorem exists_unqueried (n : nat) (Q : list (list bool)) :
  length Q < 2 ^ n -> exists a, length a = n /\ ~ In a Q.
Proof.
  intros HQ.
  set (fresh := fun x => if in_dec (list_eq_dec bool_dec) x Q then false else true).
  destruct (existsb fresh (allAssignments n)) eqn:E.
  - apply existsb_exists in E; destruct E as [x [Hx Hf]].
    exists x; split; [apply mem_allAssignments_iff; auto|].
    unfold fresh in Hf; destruct (in_dec (list_eq_dec bool_dec) x Q); [discriminate|auto].
  - exfalso.
    assert (Hincl : forall x, In x (allAssignments n) -> In x Q).
    { intros x Hx; destruct (in_dec (list_eq_dec bool_dec) x Q) as [Hin|Hnin]; auto.
      exfalso. assert (Ht : existsb fresh (allAssignments n) = true).
      { apply existsb_exists; exists x; split; auto.
        unfold fresh; destruct (in_dec (list_eq_dec bool_dec) x Q); [contradiction|auto]. }
      congruence. }
    pose proof (pigeonhole _ _ (nodup_allAssignments n) Hincl) as Hp.
    rewrite length_allAssignments in Hp; lia.
Qed.

Definition indicator (a v : list bool) : bool :=
  if list_eq_dec bool_dec v a then true else false.

Theorem nonadaptive_indistinguishable (n : nat) (Q : list (list bool)) :
  length Q < 2 ^ n ->
  exists a, length a = n /\ (exists x, length x = n /\ indicator a x = true) /\
    forall v, In v Q -> indicator a v = (fun _ => false) v.
Proof.
  intros HQ; destruct (exists_unqueried n Q HQ) as [a [Ha HaQ]].
  exists a; split; auto; split.
  - exists a; split; auto; unfold indicator; destruct (list_eq_dec bool_dec a a); congruence.
  - intros v Hv; unfold indicator; destruct (list_eq_dec bool_dec v a); auto.
    subst; contradiction.
Qed.

(** ** Adaptive decision trees *)

Inductive DTree :=
| leaf (answer : bool)
| query (v : list bool) (ifFalse ifTrue : DTree).

Fixpoint evalT (f : list bool -> bool) (t : DTree) : bool :=
  match t with
  | leaf b => b
  | query v t0 t1 => if f v then evalT f t1 else evalT f t0
  end.

Fixpoint depth (t : DTree) : nat :=
  match t with
  | leaf _ => 0
  | query _ t0 t1 => S (Nat.max (depth t0) (depth t1))
  end.

Fixpoint falsePath (t : DTree) : list (list bool) :=
  match t with
  | leaf _ => []
  | query v t0 _ => v :: falsePath t0
  end.

Lemma falsePath_length_le (t : DTree) : length (falsePath t) <= depth t.
Proof.
  induction t as [b|v t0 IH0 t1 IH1]; simpl; [lia|].
  pose proof (Nat.le_max_l (depth t0) (depth t1)); lia.
Qed.

Lemma eval_eq_of_false_on_path (t : DTree) (f g : list bool -> bool) :
  (forall v, In v (falsePath t) -> f v = false) ->
  (forall v, In v (falsePath t) -> g v = false) ->
  evalT f t = evalT g t.
Proof.
  induction t as [b|v t0 IH0 t1 IH1]; intros Hf Hg; simpl; auto.
  rewrite (Hf v (or_introl eq_refl)), (Hg v (or_introl eq_refl)).
  apply IH0; intros w Hw; [apply Hf|apply Hg]; simpl; auto.
Qed.

Definition DecidesSearch (n : nat) (t : DTree) : Prop :=
  forall f : list bool -> bool, evalT f t = true <-> exists x, length x = n /\ f x = true.

Theorem no_shallow_decision_tree (n : nat) (t : DTree) :
  depth t < 2 ^ n -> ~ DecidesSearch n t.
Proof.
  intros Hd Hdec.
  assert (Hlen : length (falsePath t) < 2 ^ n)
    by (pose proof (falsePath_length_le t); lia).
  destruct (exists_unqueried n _ Hlen) as [a [Ha HaQ]].
  assert (Hsame : evalT (indicator a) t = evalT (fun _ => false) t).
  { apply eval_eq_of_false_on_path; auto.
    intros v Hv; unfold indicator; destruct (list_eq_dec bool_dec v a); auto.
    subst; contradiction. }
  assert (H1 : evalT (indicator a) t = true).
  { apply Hdec; exists a; split; auto.
    unfold indicator; destruct (list_eq_dec bool_dec a a); congruence. }
  rewrite Hsame in H1; apply Hdec in H1.
  destruct H1 as [x [_ Hx]]; discriminate.
Qed.

Fixpoint linearTree (L : list (list bool)) : DTree :=
  match L with
  | [] => leaf false
  | v :: vs => query v (linearTree vs) (leaf true)
  end.

Lemma linearTree_depth_eq (L : list (list bool)) : depth (linearTree L) = length L.
Proof. induction L as [|v L IH]; simpl; auto. rewrite IH; lia. Qed.

Lemma linearTree_eval (L : list (list bool)) (f : list bool -> bool) :
  evalT f (linearTree L) = true <-> exists x, In x L /\ f x = true.
Proof.
  induction L as [|v L IH]; simpl.
  - split; [discriminate|intros [x [[] _]]].
  - destruct (f v) eqn:Hv.
    + split; auto. intros _; exists v; auto.
    + rewrite IH; split.
      * intros [x [Hx Hfx]]; exists x; auto.
      * intros [x [[Hx|Hx] Hfx]]; [subst; congruence|exists x; auto].
Qed.

Theorem linearTree_decides (n : nat) : DecidesSearch n (linearTree (allAssignments n)).
Proof.
  intros f; rewrite linearTree_eval; split.
  - intros [x [Hx Hfx]]; exists x; split; auto; apply mem_allAssignments_iff; auto.
  - intros [x [Hx Hfx]]; exists x; split; auto; apply mem_allAssignments_iff; auto.
Qed.

Theorem linearTree_depth (n : nat) : depth (linearTree (allAssignments n)) = 2 ^ n.
Proof. rewrite linearTree_depth_eq, length_allAssignments; auto. Qed.

(** ** CNFs as black boxes *)

Record Lit := mkLit { var : nat; pos : bool }.
Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition evalLit (a : Assignment) (l : Lit) : bool := Bool.eqb (a (var l)) (pos l).

Fixpoint evalClause (a : Assignment) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' => evalLit a l || evalClause a c'
  end.

Fixpoint evalCNF (a : Assignment) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | c :: phi' => evalClause a c && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a : Assignment, evalCNF a phi = true.

Definition VarsBelow (n : nat) (phi : CNF) : Prop :=
  forall c, In c phi -> forall l, In l c -> var l < n.

Fixpoint toAssign (v : list bool) (i : nat) : bool :=
  match v, i with
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v', S i' => toAssign v' i'
  end.

Fixpoint prefixOf (a : Assignment) (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => a 0 :: prefixOf (fun i => a (S i)) n'
  end.

Lemma length_prefixOf (a : Assignment) (n : nat) : length (prefixOf a n) = n.
Proof. revert a; induction n; intros a; simpl; auto. Qed.

Lemma toAssign_prefixOf (a : Assignment) (n i : nat) :
  i < n -> toAssign (prefixOf a n) i = a i.
Proof.
  revert a i; induction n as [|n IH]; intros a i H; [lia|].
  destruct i as [|i]; simpl; auto.
  apply (IH (fun j => a (S j))); lia.
Qed.

Lemma evalClause_congr (a b : Assignment) (n : nat) (c : Clause) :
  (forall i, i < n -> a i = b i) -> (forall l, In l c -> var l < n) ->
  evalClause a c = evalClause b c.
Proof.
  intros hab; induction c as [|l c IH]; intros hc; simpl; auto.
  unfold evalLit. rewrite (hab (var l) (hc l (or_introl eq_refl))).
  rewrite IH; auto. intros l' hl'; apply hc; simpl; auto.
Qed.

Lemma evalCNF_congr (a b : Assignment) (n : nat) (phi : CNF) :
  (forall i, i < n -> a i = b i) -> VarsBelow n phi -> evalCNF a phi = evalCNF b phi.
Proof.
  intros hab; induction phi as [|c phi IH]; intros hphi; simpl; auto.
  rewrite (evalClause_congr a b n c hab (hphi c (or_introl eq_refl))).
  rewrite IH; auto. intros c' hc'; apply hphi; simpl; auto.
Qed.

Fixpoint shiftClause (c : Clause) : Clause :=
  match c with
  | [] => []
  | l :: c' => mkLit (S (var l)) (pos l) :: shiftClause c'
  end.

Fixpoint shiftCNF (phi : CNF) : CNF :=
  match phi with
  | [] => []
  | c :: phi' => shiftClause c :: shiftCNF phi'
  end.

Lemma evalClause_shift (a : Assignment) (c : Clause) :
  evalClause a (shiftClause c) = evalClause (fun i => a (S i)) c.
Proof. induction c as [|l c IH]; simpl; auto. rewrite IH; auto. Qed.

Lemma evalCNF_shift (a : Assignment) (phi : CNF) :
  evalCNF a (shiftCNF phi) = evalCNF (fun i => a (S i)) phi.
Proof. induction phi as [|c phi IH]; simpl; auto. rewrite evalClause_shift, IH; auto. Qed.

Fixpoint pointCNF (a : list bool) : CNF :=
  match a with
  | [] => []
  | b :: a' => [mkLit 0 b] :: shiftCNF (pointCNF a')
  end.

Lemma shiftCNF_varsBelow (n : nat) (phi : CNF) :
  VarsBelow n phi -> VarsBelow (S n) (shiftCNF phi).
Proof.
  induction phi as [|c phi IH]; intros H c' Hc' l Hl; simpl in Hc'; [contradiction|].
  destruct Hc' as [Hc'|Hc'].
  - subst c'. assert (Hc : forall l, In l c -> var l < n) by (apply H; simpl; auto).
    clear H IH. induction c as [|l0 c IHc]; simpl in Hl; [contradiction|].
    destruct Hl as [Hl|Hl].
    + subst; simpl. pose proof (Hc l0 (or_introl eq_refl)); lia.
    + apply IHc; auto. intros l' Hl'; apply Hc; simpl; auto.
  - apply (IH (fun c'' Hc'' => H c'' (or_intror Hc'')) c' Hc' l Hl).
Qed.

Lemma pointCNF_varsBelow (a : list bool) : VarsBelow (length a) (pointCNF a).
Proof.
  induction a as [|b a IH]; intros c Hc l Hl; simpl in Hc; [contradiction|].
  destruct Hc as [Hc|Hc].
  - subst; simpl in Hl; destruct Hl as [Hl|[]]; subst; simpl; lia.
  - apply (shiftCNF_varsBelow _ _ IH c Hc l Hl).
Qed.

Theorem pointCNF_iff (a v : list bool) :
  length v = length a -> (evalCNF (toAssign v) (pointCNF a) = true <-> v = a).
Proof.
  revert v; induction a as [|b a IH]; intros v H.
  - destruct v; simpl in *; [split; auto|discriminate].
  - destruct v as [|c v]; simpl in H; [discriminate|].
    injection H; intros H'. simpl. rewrite evalCNF_shift.
    change (fun i => toAssign (c :: v) (S i)) with (toAssign v).
    unfold evalLit; simpl. rewrite orb_false_r, andb_true_iff, IH; auto.
    rewrite eqb_true_iff. split.
    + intros [H1 H2]; subst; auto.
    + intros Heq; injection Heq; auto.
Qed.

Theorem pointCNF_satisfiable (a : list bool) : Satisfiable (pointCNF a).
Proof. exists (toAssign a); apply pointCNF_iff; auto. Qed.

Theorem failed_trials_do_not_certify (n : nat) (Q : list (list bool)) :
  length Q < 2 ^ n ->
  exists phi : CNF, VarsBelow n phi /\ Satisfiable phi /\
    forall v, In v Q -> evalCNF (toAssign v) phi = false.
Proof.
  intros HQ.
  set (norm := fun v => prefixOf (toAssign v) n).
  assert (Hlen : length (map norm Q) < 2 ^ n) by (rewrite length_map; auto).
  destruct (exists_unqueried n _ Hlen) as [a [Ha HaQ]].
  assert (Hvb : VarsBelow n (pointCNF a)) by (rewrite <- Ha; apply pointCNF_varsBelow).
  exists (pointCNF a); split; auto; split; [apply pointCNF_satisfiable|].
  intros v Hv.
  rewrite (evalCNF_congr (toAssign v) (toAssign (norm v)) n); auto.
  - destruct (evalCNF (toAssign (norm v)) (pointCNF a)) eqn:He; auto.
    exfalso. apply pointCNF_iff in He.
    + apply HaQ; rewrite <- He; apply in_map; auto.
    + unfold norm; rewrite length_prefixOf; auto.
  - intros i Hi; unfold norm; rewrite toAssign_prefixOf; auto.
Qed.

Definition oracle (phi : CNF) : list bool -> bool := fun v => evalCNF (toAssign v) phi.

Theorem no_shallow_cnf_blackbox (n : nat) (t : DTree) :
  depth t < 2 ^ n ->
  ~ (forall phi : CNF, VarsBelow n phi -> (evalT (oracle phi) t = true <-> Satisfiable phi)).
Proof.
  intros Hd Hdec.
  assert (Hlen : length (falsePath t) < 2 ^ n)
    by (pose proof (falsePath_length_le t); lia).
  destruct (failed_trials_do_not_certify n _ Hlen) as [phi [Hphi [Hsat Hfalse]]].
  assert (Hempty : VarsBelow n [[]]).
  { intros c Hc l Hl; simpl in Hc; destruct Hc as [Hc|[]]; subst; contradiction. }
  assert (Hsame : evalT (oracle phi) t = evalT (oracle [[]]) t).
  { apply eval_eq_of_false_on_path; auto. }
  assert (H1 : evalT (oracle phi) t = true) by (apply Hdec; auto).
  rewrite Hsame in H1. apply (Hdec [[]] Hempty) in H1.
  destruct H1 as [a Ha]; simpl in Ha; discriminate.
Qed.
