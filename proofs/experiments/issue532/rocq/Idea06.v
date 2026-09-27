(* Issue #532, Idea 06: local search and potential functions.

   Proved for all parameters:
   - line landscapes: state 0 is a strict local minimum of cost M, the
     global minimum 0 sits at state n, and improving walks from 0..n-2 never
     reach it (line_basin, line_never_reaches_global);
   - SAT with cost = number of falsified clauses: for every radius k,
     trapCNF k is satisfiable, but all-false has cost 1 and every assignment
     within k flips of it costs at least 1 (bounded_flip_not_exact);
   - an exact neighbourhood of size one exists for every CNF
     (exists_size_one_exact_neighbourhood), so size is not the obstacle;
   - conditional theorem: with any exact neighbourhood, local search with
     fuel unsatCount a phi + 1 decides satisfiability, using at most
     fuel * B neighbour evaluations (exact_local_search_decides,
     localSearch_evals_le).

   Verdict: refuted as a route (general theorem). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(** ** CNF syntax and semantics *)

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

(** ** Enumerating all assignments *)

Fixpoint allAssignments (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allAssignments n') ++ map (cons true) (allAssignments n')
  end.

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

Lemma length_prefixOf (a : Assignment) (n : nat) : length (prefixOf a n) = n.
Proof. revert a; induction n; intros a; simpl; auto. Qed.

Lemma toAssign_prefixOf (a : Assignment) (n i : nat) :
  i < n -> toAssign (prefixOf a n) i = a i.
Proof.
  revert a i; induction n as [|n IH]; intros a i H; [lia|].
  destruct i as [|i]; simpl; auto.
  apply (IH (fun j => a (S j))); lia.
Qed.

(** ** Number of variables *)

Fixpoint clauseBound (c : Clause) : nat :=
  match c with
  | [] => 0
  | l :: c' => Nat.max (S (var l)) (clauseBound c')
  end.

Fixpoint numVars (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => Nat.max (clauseBound c) (numVars phi')
  end.

Lemma clauseBound_cons (l : Lit) (c : Clause) :
  clauseBound (l :: c) = Nat.max (S (var l)) (clauseBound c).
Proof. reflexivity. Qed.

Lemma numVars_cons (c : Clause) (phi : CNF) :
  numVars (c :: phi) = Nat.max (clauseBound c) (numVars phi).
Proof. reflexivity. Qed.

Lemma lt_clauseBound (c : Clause) : forall l, In l c -> var l < clauseBound c.
Proof.
  induction c as [|l c IH]; intros l' Hl'; [contradiction|].
  change (clauseBound (l :: c)) with (Nat.max (S (var l)) (clauseBound c)).
  destruct Hl' as [H|H]; [subst; lia|]. specialize (IH l' H); lia.
Qed.

Lemma varsBelow_numVars (phi : CNF) : VarsBelow (numVars phi) phi.
Proof.
  induction phi as [|c phi IH]; intros c' Hc' l Hl; [contradiction|].
  change (numVars (c :: phi)) with (Nat.max (clauseBound c) (numVars phi)).
  destruct Hc' as [H|H].
  - subst; pose proof (lt_clauseBound c' l Hl); lia.
  - pose proof (IH c' H l Hl); lia.
Qed.


(** ** Local minima *)

Definition IsLocalMin {A : Type} (cost : A -> nat) (nbr : A -> list A) (s : A) : Prop :=
  forall t, In t (nbr s) -> cost s <= cost t.

Definition ExactAll {A : Type} (cost : A -> nat) (nbr : A -> list A) : Prop :=
  forall s, IsLocalMin cost nbr s -> forall t, cost s <= cost t.

Inductive ImpPath {A : Type} (cost : A -> nat) (nbr : A -> list A) : A -> A -> Prop :=
  | ImpPath_refl : forall s, ImpPath cost nbr s s
  | ImpPath_step : forall s t u, In t (nbr s) -> cost t < cost s ->
      ImpPath cost nbr t u -> ImpPath cost nbr s u.

(** ** The deceptive line landscape *)

Definition lineNbr (n i : nat) : list nat :=
  (if 0 <? i then [i - 1] else []) ++ (if i <? n then [S i] else []).

Definition trapCost (M n i : nat) : nat := if Nat.eqb i n then 0 else M + i.

Lemma mem_lineNbr : forall n i t, In t (lineNbr n i) ->
  (0 < i /\ t = i - 1) \/ (i < n /\ t = S i).
Proof.
  intros n i t H. unfold lineNbr in H. apply in_app_or in H.
  destruct H as [H|H].
  - destruct (0 <? i) eqn:E; simpl in H; [|contradiction].
    apply Nat.ltb_lt in E. destruct H as [H|H]; [|contradiction]. left; lia.
  - destruct (i <? n) eqn:E; simpl in H; [|contradiction].
    apply Nat.ltb_lt in E. destruct H as [H|H]; [|contradiction]. right; lia.
Qed.

Theorem line_strict_local_min : forall M n, 2 <= n ->
  forall t, In t (lineNbr n 0) -> trapCost M n 0 < trapCost M n t.
Proof.
  intros M n Hn t Ht. destruct (mem_lineNbr n 0 t Ht) as [[H1 _]|[_ H2]]; [lia|].
  subst t. unfold trapCost.
  destruct (Nat.eqb 0 n) eqn:E0; [apply Nat.eqb_eq in E0; lia|].
  destruct (Nat.eqb 1 n) eqn:E1; [apply Nat.eqb_eq in E1; lia|]. lia.
Qed.

Theorem line_global_min : forall M n t, trapCost M n n <= trapCost M n t.
Proof. intros M n t. unfold trapCost. rewrite Nat.eqb_refl. lia. Qed.

Theorem line_local_not_global : forall M n, 1 <= M -> 2 <= n ->
  IsLocalMin (trapCost M n) (lineNbr n) 0 /\ trapCost M n n < trapCost M n 0.
Proof.
  intros M n HM Hn. split.
  - intros t Ht. apply Nat.lt_le_incl, line_strict_local_min; assumption.
  - unfold trapCost. rewrite Nat.eqb_refl.
    destruct (Nat.eqb 0 n) eqn:E0; [apply Nat.eqb_eq in E0; lia|]. lia.
Qed.

Theorem line_basin : forall M n i t, i + 2 <= n ->
  ImpPath (trapCost M n) (lineNbr n) i t -> t + 2 <= n.
Proof.
  intros M n i t Hi Hp. induction Hp as [s|s u w Hmem Hlt Hp IH]; [exact Hi|].
  apply IH. destruct (mem_lineNbr n s u Hmem) as [[_ H2]|[_ H2]]; [lia|].
  subst u. unfold trapCost in Hlt.
  destruct (Nat.eqb s n) eqn:Es; [apply Nat.eqb_eq in Es; lia|].
  destruct (Nat.eqb (S s) n) eqn:Es1.
  - apply Nat.eqb_eq in Es1. lia.
  - lia.
Qed.

Theorem line_never_reaches_global : forall M n i, i + 2 <= n ->
  ~ ImpPath (trapCost M n) (lineNbr n) i n.
Proof. intros M n i Hi Hp. pose proof (line_basin M n i n Hi Hp). lia. Qed.

(** ** Exact neighbourhoods *)

Theorem full_neighbourhood_exact : forall (A : Type) (cost : A -> nat) (U : list A),
  (forall t, In t U) -> ExactAll cost (fun _ => U).
Proof. intros A cost U HU s Hs t. apply Hs, HU. Qed.

Theorem singleton_exact_neighbourhood : forall (A : Type) (cost : A -> nat) (best : A),
  (forall t, cost best <= cost t) -> ExactAll cost (fun _ => [best]).
Proof.
  intros A cost best Hb s Hs t. specialize (Hs best (or_introl eq_refl)).
  specialize (Hb t). lia.
Qed.

Fixpoint Descending {A : Type} (cost : A -> nat) (l : list A) : Prop :=
  match l with
  | [] => True
  | s :: rest =>
      match rest with
      | [] => True
      | t :: _ => cost t < cost s /\ Descending cost rest
      end
  end.

Theorem descending_length_le : forall (A : Type) (cost : A -> nat) (rest : list A) (s : A),
  Descending cost (s :: rest) -> length rest <= cost s.
Proof.
  intros A cost rest. induction rest as [|t rest IH]; intros s H; simpl; [lia|].
  destruct H as [Hlt Hd]. specialize (IH t Hd). lia.
Qed.

(** ** Local search with an evaluation count *)

Fixpoint firstImproving {A : Type} (cost : A -> nat) (s : A) (L : list A) : option A :=
  match L with
  | [] => None
  | t :: ts => if cost t <? cost s then Some t else firstImproving cost s ts
  end.

Lemma firstImproving_some : forall (A : Type) (cost : A -> nat) (s t : A) (L : list A),
  firstImproving cost s L = Some t -> In t L /\ cost t < cost s.
Proof.
  intros A cost s t L. induction L as [|u L IH]; simpl; intro H; [discriminate|].
  destruct (cost u <? cost s) eqn:E.
  - inversion H; subst. apply Nat.ltb_lt in E. split; [left; reflexivity|exact E].
  - destruct (IH H) as [H1 H2]. split; [right; exact H1|exact H2].
Qed.

Lemma firstImproving_none : forall (A : Type) (cost : A -> nat) (s : A) (L : list A),
  firstImproving cost s L = None -> forall t, In t L -> cost s <= cost t.
Proof.
  intros A cost s L. induction L as [|u L IH]; simpl; intros H t Ht; [contradiction|].
  destruct (cost u <? cost s) eqn:E; [discriminate|].
  apply Nat.ltb_ge in E. destruct Ht as [Ht|Ht]; [subst; exact E|exact (IH H t Ht)].
Qed.

Fixpoint localSearch {A : Type} (cost : A -> nat) (nbr : A -> list A) (f : nat) (s : A) : A :=
  match f with
  | 0 => s
  | S f' =>
      match firstImproving cost s (nbr s) with
      | None => s
      | Some t => localSearch cost nbr f' t
      end
  end.

Fixpoint searchEvals {A : Type} (cost : A -> nat) (nbr : A -> list A) (f : nat) (s : A) : nat :=
  match f with
  | 0 => 0
  | S f' =>
      length (nbr s) +
        match firstImproving cost s (nbr s) with
        | None => 0
        | Some t => searchEvals cost nbr f' t
        end
  end.

Theorem localSearch_localMin : forall (A : Type) (cost : A -> nat) (nbr : A -> list A) f s,
  cost s < f -> IsLocalMin cost nbr (localSearch cost nbr f s).
Proof.
  intros A cost nbr f. induction f as [|f IH]; intros s Hf; [lia|]. simpl.
  destruct (firstImproving cost s (nbr s)) as [t|] eqn:E.
  - destruct (firstImproving_some A cost s t (nbr s) E) as [_ Hlt]. apply IH. lia.
  - exact (firstImproving_none A cost s (nbr s) E).
Qed.

Theorem localSearch_evals_le : forall (A : Type) (cost : A -> nat) (nbr : A -> list A) B,
  (forall s, length (nbr s) <= B) -> forall f s, searchEvals cost nbr f s <= f * B.
Proof.
  intros A cost nbr B HB f. induction f as [|f IH]; intro s; simpl; [lia|].
  pose proof (HB s).
  destruct (firstImproving cost s (nbr s)) as [t|]; [pose proof (IH t)|]; lia.
Qed.

(** ** SAT as a local search problem *)

Fixpoint unsatCount (a : Assignment) (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => (if evalClause a c then 0 else 1) + unsatCount a phi'
  end.

Lemma unsatCount_cons : forall a c phi,
  unsatCount a (c :: phi) = (if evalClause a c then 0 else 1) + unsatCount a phi.
Proof. reflexivity. Qed.

Theorem unsatCount_eq_zero_iff : forall a phi, unsatCount a phi = 0 <-> evalCNF a phi = true.
Proof.
  intros a phi. induction phi as [|c phi IH]; simpl; [split; reflexivity|].
  destruct (evalClause a c); simpl; [exact IH|split; intro H; discriminate].
Qed.

Lemma unsatCount_congr : forall (a b : Assignment) n phi,
  (forall i, i < n -> a i = b i) -> VarsBelow n phi -> unsatCount a phi = unsatCount b phi.
Proof.
  intros a b n phi Hab. induction phi as [|c phi IH]; intro Hphi; simpl; [reflexivity|].
  rewrite (evalClause_congr a b n c Hab (Hphi c (or_introl eq_refl))).
  rewrite IH; [reflexivity|]. intros c' Hc'. apply Hphi. right; exact Hc'.
Qed.

Theorem exact_local_search_decides : forall phi (nbr : Assignment -> list Assignment),
  ExactAll (fun a => unsatCount a phi) nbr -> forall a,
  evalCNF (localSearch (fun b => unsatCount b phi) nbr (S (unsatCount a phi)) a) phi = true
    <-> Satisfiable phi.
Proof.
  intros phi nbr Hex a. split.
  - intro H. eexists; exact H.
  - intros [t Ht].
    pose proof (localSearch_localMin _ (fun b => unsatCount b phi) nbr
      (S (unsatCount a phi)) a (Nat.lt_succ_diag_r _)) as Hloc.
    pose proof (Hex _ Hloc t) as Hle. cbv beta in Hle.
    apply unsatCount_eq_zero_iff in Ht.
    apply unsatCount_eq_zero_iff. lia.
Qed.

Fixpoint argminBy {A : Type} (f : A -> nat) (o : A) (os : list A) : A :=
  match os with
  | [] => o
  | p :: ps =>
      let q := argminBy f p ps in
      if f q <? f o then q else o
  end.

Lemma argminBy_le : forall (A : Type) (f : A -> nat) (os : list A) (o : A) (p : A),
  In p (o :: os) -> f (argminBy f o os) <= f p.
Proof.
  intros A f os. induction os as [|q qs IH]; intros o p Hp; simpl.
  - destruct Hp as [Hp|Hp]; [subst; lia|contradiction].
  - destruct (f (argminBy f q qs) <? f o) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct Hp as [Hp|Hp].
      * subst; lia.
      * apply IH; exact Hp.
    + apply Nat.ltb_ge in Hlt.
      destruct Hp as [Hp|Hp].
      * subst; lia.
      * specialize (IH q p Hp); lia.
Qed.

Definition bestAssign (phi : CNF) : Assignment :=
  toAssign (argminBy (fun v => unsatCount (toAssign v) phi) [] (allAssignments (numVars phi))).

Theorem bestAssign_min : forall phi t, unsatCount (bestAssign phi) phi <= unsatCount t phi.
Proof.
  intros phi t.
  assert (Hmem : In (prefixOf t (numVars phi)) (allAssignments (numVars phi))).
  { apply mem_allAssignments_iff. apply length_prefixOf. }
  pose proof (argminBy_le _ (fun v => unsatCount (toAssign v) phi) (allAssignments (numVars phi))
    [] (prefixOf t (numVars phi)) (or_intror Hmem)) as H1.
  pose proof (unsatCount_congr (toAssign (prefixOf t (numVars phi))) t (numVars phi) phi
    (fun i Hi => toAssign_prefixOf t (numVars phi) i Hi) (varsBelow_numVars phi)) as H2.
  unfold bestAssign. simpl in H1. lia.
Qed.

Theorem exists_size_one_exact_neighbourhood :
  exists N : CNF -> Assignment -> list Assignment,
    (forall phi a, length (N phi a) = 1) /\
    forall phi, ExactAll (fun a => unsatCount a phi) (N phi).
Proof.
  exists (fun phi _ => [bestAssign phi]). split; [reflexivity|].
  intro phi. apply singleton_exact_neighbourhood. apply bestAssign_min.
Qed.

(** ** Fixed-radius flip neighbourhoods are not exact *)

Definition Within (k n : nat) (a b : Assignment) : Prop :=
  exists S, length S <= k /\ forall i, i < n -> a i <> b i -> In i S.

Definition trapPairs (k : nat) : CNF :=
  flat_map (fun i => map (fun j => [mkLit i false; mkLit j true]) (seq 0 (S k))) (seq 0 (S k)).

Definition trapCNF (k : nat) : CNF :=
  map (fun i => mkLit i true) (seq 0 (S k)) :: trapPairs k.

Lemma evalClause_true_iff : forall a c,
  evalClause a c = true <-> exists l, In l c /\ evalLit a l = true.
Proof.
  intros a c. induction c as [|l c IH]; simpl.
  - split; [discriminate|intros [l [[] _]]].
  - rewrite orb_true_iff, IH. split.
    + intros [H|[l' [H1 H2]]]; [exists l; auto|exists l'; auto].
    + intros [l' [[H1|H1] H2]]; [subst; left; exact H2|right; exists l'; auto].
Qed.

Lemma evalCNF_true_iff : forall a phi,
  evalCNF a phi = true <-> forall c, In c phi -> evalClause a c = true.
Proof.
  intros a phi. induction phi as [|c phi IH]; simpl.
  - split; [intros _ c []|reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] c' [H|H]; [subst; exact H1|exact (H2 c' H)].
    + intro H. split; [apply H; left; reflexivity|intros c' Hc'; apply H; right; exact Hc'].
Qed.

Lemma mem_trapPairs : forall k c, In c (trapPairs k) <->
  exists i j, i < S k /\ j < S k /\ c = [mkLit i false; mkLit j true].
Proof.
  intros k c. unfold trapPairs. rewrite in_flat_map. split.
  - intros [i [Hi Hc]]. apply in_map_iff in Hc. destruct Hc as [j [Hc Hj]].
    apply in_seq in Hi. apply in_seq in Hj. exists i, j. repeat split; auto; lia.
  - intros [i [j [Hi [Hj Hc]]]]. exists i. split; [apply in_seq; lia|].
    apply in_map_iff. exists j. split; [auto|apply in_seq; lia].
Qed.

Theorem trapCNF_allTrue : forall k, evalCNF (fun _ => true) (trapCNF k) = true.
Proof.
  intro k. apply evalCNF_true_iff. intros c [Hc|Hc].
  - subst c. apply evalClause_true_iff. exists (mkLit 0 true). split; [|reflexivity].
    apply in_map_iff. exists 0. split; [reflexivity|apply in_seq; lia].
  - apply mem_trapPairs in Hc. destruct Hc as [i [j [_ [_ Hc]]]]. subst c. reflexivity.
Qed.

Theorem trapCNF_allFalse_cost : forall k, unsatCount (fun _ => false) (trapCNF k) = 1.
Proof.
  intro k.
  assert (Hfirst : evalClause (fun _ => false) (map (fun i => mkLit i true) (seq 0 (S k))) = false).
  { destruct (evalClause (fun _ => false) (map (fun i => mkLit i true) (seq 0 (S k)))) eqn:E;
      [|reflexivity].
    apply evalClause_true_iff in E. destruct E as [l [Hl Hev]].
    apply in_map_iff in Hl. destruct Hl as [i [Hl _]]. subst l. discriminate. }
  assert (Hrest : evalCNF (fun _ => false) (trapPairs k) = true).
  { apply evalCNF_true_iff. intros c Hc. apply mem_trapPairs in Hc.
    destruct Hc as [i [j [_ [_ Hc]]]]. subst c. reflexivity. }
  unfold trapCNF. rewrite unsatCount_cons, Hfirst.
  apply unsatCount_eq_zero_iff in Hrest. rewrite Hrest. reflexivity.
Qed.

Lemma missing_below : forall k (S : list nat), length S <= k ->
  exists i, i < Datatypes.S k /\ ~ In i S.
Proof.
  intros k S HS.
  destruct (existsb (fun i => if in_dec Nat.eq_dec i S then false else true)
    (seq 0 (Datatypes.S k))) eqn:E.
  - apply existsb_exists in E. destruct E as [i [Hi Hb]].
    destruct (in_dec Nat.eq_dec i S) as [Hin|Hin]; [discriminate|].
    apply in_seq in Hi. exists i. split; [lia|exact Hin].
  - exfalso.
    assert (Hsub : incl (seq 0 (Datatypes.S k)) S).
    { intros i Hi. destruct (in_dec Nat.eq_dec i S) as [Hin|Hin]; [exact Hin|].
      assert (Ht : existsb (fun i => if in_dec Nat.eq_dec i S then false else true)
        (seq 0 (Datatypes.S k)) = true).
      { apply existsb_exists. exists i. split; [exact Hi|].
        destruct (in_dec Nat.eq_dec i S); [contradiction|reflexivity]. }
      rewrite Ht in E. discriminate. }
    assert (Hl : length (seq 0 (Datatypes.S k)) <= length S)
      by (apply NoDup_incl_length; [apply seq_NoDup|exact Hsub]).
    rewrite length_seq in Hl. lia.
Qed.

Theorem trapCNF_near_allFalse : forall k (b : Assignment),
  Within k (S k) (fun _ => false) b -> evalCNF b (trapCNF k) = false.
Proof.
  intros k b [S [HS Hcov]].
  destruct (missing_below k S HS) as [i [Hi HiS]].
  assert (Hbi : b i = false).
  { destruct (b i) eqn:Hb; [|reflexivity].
    exfalso. apply HiS. apply Hcov; [exact Hi|rewrite Hb; discriminate]. }
  destruct (evalCNF b (trapCNF k)) eqn:Hall; [|reflexivity].
  exfalso. pose proof (proj1 (evalCNF_true_iff b _) Hall) as Hall'.
  destruct (existsb (fun j => b j) (seq 0 (Datatypes.S k))) eqn:E.
  - apply existsb_exists in E. destruct E as [j [Hj Hbj]]. apply in_seq in Hj.
    assert (Hmem : In [mkLit j false; mkLit i true] (trapCNF k)).
    { right. apply mem_trapPairs. exists j, i. repeat split; lia. }
    specialize (Hall' _ Hmem). simpl in Hall'. unfold evalLit in Hall'. simpl in Hall'.
    rewrite Hbj, Hbi in Hall'. discriminate.
  - specialize (Hall' _ (or_introl eq_refl)).
    apply evalClause_true_iff in Hall'. destruct Hall' as [l [Hl Hev]].
    apply in_map_iff in Hl. destruct Hl as [j [Hl Hj]]. subst l.
    unfold evalLit in Hev. simpl in Hev.
    assert (Ht : existsb (fun j => b j) (seq 0 (Datatypes.S k)) = true).
    { apply existsb_exists. exists j. split; [exact Hj|].
      destruct (b j); [reflexivity|discriminate]. }
    rewrite Ht in E. discriminate.
Qed.

Theorem bounded_flip_not_exact : forall k,
  Satisfiable (trapCNF k) /\ unsatCount (fun _ => false) (trapCNF k) = 1 /\
  forall b, Within k (S k) (fun _ => false) b ->
    unsatCount (fun _ => false) (trapCNF k) <= unsatCount b (trapCNF k).
Proof.
  intro k. split; [exists (fun _ => true); apply trapCNF_allTrue|].
  split; [apply trapCNF_allFalse_cost|].
  intros b Hb. rewrite trapCNF_allFalse_cost.
  pose proof (trapCNF_near_allFalse k b Hb) as H.
  destruct (unsatCount b (trapCNF k)) eqn:E; [|lia].
  apply unsatCount_eq_zero_iff in E. rewrite E in H. discriminate.
Qed.
