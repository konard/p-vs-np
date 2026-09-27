(* Issue #532, Idea 28: definitional extensions (Tseitin transformation).

   Verdict: correct tool, insufficient alone (general theorem proved).
   Tseitin reduces formula satisfiability to 3-SAT with linear size
   (hardness preservation, not easiness); adding definitions to resolution
   gives extended resolution, whose superpolynomial lower bounds are open.

   Same content as ../lean/Idea28.lean (Lean Formula.eval_congr is
   formula_eval_congr here; Lean constructors ERDerives.start/res/ext are
   er_start/er_res/er_ext):
   - tseitin_equisat, tseitinCNF_length (<= 3 * gates + 1),
     tseitinCNF_width (<= 3 literals), tseitinCNF_vars, tseitin_next;
   - transfer, define_and_sat_iff;
   - defGate_iff (extension clauses y <-> l1 /\ l2 for literals), er_sat,
     er_sound, and the open obligation ERSuperpolyLowerBound (a definition),
     with obligation_excludes_poly_bound.
   See ../ideas/Idea28.md. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Record Lit := mkLit { var : nat; pos : bool }.

Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition evalLit (a : Assignment) (l : Lit) : bool :=
  if pos l then a (var l) else negb (a (var l)).

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

Definition Satisfiable (phi : CNF) : Prop := exists a, evalCNF a phi = true.

Definition clauseVars (c : Clause) : list nat := map var c.

Fixpoint vars (phi : CNF) : list nat :=
  match phi with
  | [] => []
  | c :: phi' => clauseVars c ++ vars phi'
  end.

Lemma evalCNF_append : forall a (phi psi : CNF),
  evalCNF a (phi ++ psi) = evalCNF a phi && evalCNF a psi.
Proof.
  intros a phi psi; induction phi as [|c phi IH]; simpl.
  - reflexivity.
  - rewrite IH, andb_assoc; reflexivity.
Qed.

Lemma vars_append : forall phi psi : CNF, vars (phi ++ psi) = vars phi ++ vars psi.
Proof.
  intros phi psi; induction phi as [|c phi IH]; simpl.
  - reflexivity.
  - rewrite IH, app_assoc; reflexivity.
Qed.

Lemma evalClause_congr : forall (a b : Assignment) (c : Clause),
  (forall v, In v (clauseVars c) -> a v = b v) -> evalClause a c = evalClause b c.
Proof.
  intros a b c; induction c as [|l c IH]; intros H; simpl.
  - reflexivity.
  - assert (Hl : a (var l) = b (var l)) by (apply H; simpl; left; reflexivity).
    rewrite IH.
    + unfold evalLit; rewrite Hl; reflexivity.
    + intros v Hv; apply H; simpl; right; exact Hv.
Qed.

(* Locality of evaluation. *)
Theorem eval_congr : forall (a b : Assignment) (phi : CNF),
  (forall v, In v (vars phi) -> a v = b v) -> evalCNF a phi = evalCNF b phi.
Proof.
  intros a b phi; induction phi as [|c phi IH]; intros H; simpl.
  - reflexivity.
  - rewrite (evalClause_congr a b c), IH.
    + reflexivity.
    + intros v Hv; apply H; simpl; apply in_or_app; right; exact Hv.
    + intros v Hv; apply H; simpl; apply in_or_app; left; exact Hv.
Qed.

Lemma evalClause_iff : forall a (c : Clause),
  evalClause a c = true <-> exists l, In l c /\ evalLit a l = true.
Proof.
  intros a c; induction c as [|l c IH]; simpl.
  - split; [discriminate | intros [l [[] _]]].
  - rewrite orb_true_iff, IH; split.
    + intros [H | [l' [Hin H]]]; [exists l; auto | exists l'; auto].
    + intros [l' [[Heq | Hin] H]]; [subst; left; exact H | right; exists l'; auto].
Qed.
Lemma evalCNF_iff : forall a (phi : CNF),
  evalCNF a phi = true <-> forall c, In c phi -> evalClause a c = true.
Proof.
  intros a phi; induction phi as [|c phi IH]; simpl.
  - split; [intros _ c [] | reflexivity].
  - rewrite andb_true_iff, IH; split.
    + intros [H1 H2] d [Hd | Hd]; [subst; exact H1 | apply H2; exact Hd].
    + intros H; split; [apply H; left; reflexivity | intros d Hd; apply H; right; exact Hd].
Qed.

Definition update (b : Assignment) (y : nat) (val : bool) : Assignment :=
  fun w => if Nat.eq_dec w y then val else b w.

Lemma update_same : forall b y val, update b y val y = val.
Proof. intros; unfold update; destruct (Nat.eq_dec y y); [reflexivity | contradiction]. Qed.

Lemma update_ne : forall b y val w, w <> y -> update b y val w = b w.
Proof. intros; unfold update; destruct (Nat.eq_dec w y); [contradiction | reflexivity]. Qed.

Lemma update_evalCNF : forall b y val phi,
  (forall v, In v (vars phi) -> v < y) -> evalCNF (update b y val) phi = evalCNF b phi.
Proof.
  intros b y val phi H; apply eval_congr; intros v Hv; apply update_ne.
  specialize (H v Hv); lia.
Qed.

(* Gate clauses *)

Definition pl (v : nat) : Lit := mkLit v true.
Definition nl (v : nat) : Lit := mkLit v false.

Definition negGate (y x : nat) : CNF := [[pl y; pl x]; [nl y; nl x]].
Definition andGate (y x z : nat) : CNF := [[nl y; pl x]; [nl y; pl z]; [pl y; nl x; nl z]].
Definition orGate (y x z : nat) : CNF := [[pl y; nl x]; [pl y; nl z]; [nl y; pl x; pl z]].

Lemma negGate_iff : forall b y x, evalCNF b (negGate y x) = true <-> b y = negb (b x).
Proof.
  intros b y x; unfold negGate; simpl; unfold evalLit, pl, nl; simpl.
  destruct (b y), (b x); simpl; split; intros; congruence.
Qed.

Lemma andGate_iff : forall b y x z,
  evalCNF b (andGate y x z) = true <-> b y = (b x && b z).
Proof.
  intros b y x z; unfold andGate; simpl; unfold evalLit, pl, nl; simpl.
  destruct (b y), (b x), (b z); simpl; split; intros; congruence.
Qed.

Lemma orGate_iff : forall b y x z,
  evalCNF b (orGate y x z) = true <-> b y = (b x || b z).
Proof.
  intros b y x z; unfold orGate; simpl; unfold evalLit, pl, nl; simpl.
  destruct (b y), (b x), (b z); simpl; split; intros; congruence.
Qed.

Lemma negGate_vars : forall y x v, In v (vars (negGate y x)) -> v = y \/ v = x.
Proof. intros y x v H; unfold negGate, pl, nl in H; simpl in H; lia. Qed.

Lemma andGate_vars : forall y x z v, In v (vars (andGate y x z)) -> v = y \/ v = x \/ v = z.
Proof. intros y x z v H; unfold andGate, pl, nl in H; simpl in H; lia. Qed.

Lemma orGate_vars : forall y x z v, In v (vars (orGate y x z)) -> v = y \/ v = x \/ v = z.
Proof. intros y x z v H; unfold orGate, pl, nl in H; simpl in H; lia. Qed.

(* Propositional formulas *)

Inductive Formula : Type :=
| fvar : nat -> Formula
| fneg : Formula -> Formula
| fconj : Formula -> Formula -> Formula
| fdisj : Formula -> Formula -> Formula.

Fixpoint eval (a : Assignment) (f : Formula) : bool :=
  match f with
  | fvar i => a i
  | fneg f1 => negb (eval a f1)
  | fconj f1 f2 => eval a f1 && eval a f2
  | fdisj f1 f2 => eval a f1 || eval a f2
  end.

Fixpoint gates (f : Formula) : nat :=
  match f with
  | fvar _ => 0
  | fneg f1 => gates f1 + 1
  | fconj f1 f2 => gates f1 + gates f2 + 1
  | fdisj f1 f2 => gates f1 + gates f2 + 1
  end.

Fixpoint bound (f : Formula) : nat :=
  match f with
  | fvar i => S i
  | fneg f1 => bound f1
  | fconj f1 f2 => Nat.max (bound f1) (bound f2)
  | fdisj f1 f2 => Nat.max (bound f1) (bound f2)
  end.

Lemma max_le_l : forall a b n, Nat.max a b <= n -> a <= n.
Proof. intros a b n H; eapply Nat.le_trans; [apply Nat.le_max_l | exact H]. Qed.

Lemma max_le_r : forall a b n, Nat.max a b <= n -> b <= n.
Proof. intros a b n H; eapply Nat.le_trans; [apply Nat.le_max_r | exact H]. Qed.

(* Lean: Formula.eval_congr *)
Lemma formula_eval_congr : forall a b f,
  (forall v, v < bound f -> a v = b v) -> eval a f = eval b f.
Proof.
  intros a b f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros H; simpl in *.
  - apply H; lia.
  - rewrite IH; [reflexivity | exact H].
  - rewrite IHf, IHg; [reflexivity | |]; intros v Hv; apply H.
    + apply Nat.lt_le_trans with (bound g); [exact Hv | apply Nat.le_max_r].
    + apply Nat.lt_le_trans with (bound f); [exact Hv | apply Nat.le_max_l].
  - rewrite IHf, IHg; [reflexivity | |]; intros v Hv; apply H.
    + apply Nat.lt_le_trans with (bound g); [exact Hv | apply Nat.le_max_r].
    + apply Nat.lt_le_trans with (bound f); [exact Hv | apply Nat.le_max_l].
Qed.

(* The Tseitin transformation *)

Record TOut := mkT { out : nat; cls : CNF; next : nat }.

Fixpoint tseitin (f : Formula) (n : nat) : TOut :=
  match f with
  | fvar i => mkT i [] n
  | fneg f1 =>
      let r := tseitin f1 n in
      mkT (next r) (cls r ++ negGate (next r) (out r)) (S (next r))
  | fconj f1 f2 =>
      let r := tseitin f1 n in
      let s := tseitin f2 (next r) in
      mkT (next s) ((cls r ++ cls s) ++ andGate (next s) (out r) (out s)) (S (next s))
  | fdisj f1 f2 =>
      let r := tseitin f1 n in
      let s := tseitin f2 (next r) in
      mkT (next s) ((cls r ++ cls s) ++ orGate (next s) (out r) (out s)) (S (next s))
  end.

Definition tseitinCNF (f : Formula) : CNF :=
  cls (tseitin f (bound f)) ++ [[pl (out (tseitin f (bound f)))]].

(* Exactly one fresh variable per gate. *)
Theorem tseitin_next : forall f n, next (tseitin f n) = n + gates f.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n; simpl.
  - lia.
  - rewrite IH; lia.
  - rewrite IHg, IHf; lia.
  - rewrite IHg, IHf; lia.
Qed.

(* At most three clauses per gate. *)
Theorem tseitin_length : forall f n, length (cls (tseitin f n)) <= 3 * gates f.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n; simpl.
  - lia.
  - rewrite length_app; specialize (IH n); unfold negGate; simpl length; lia.
  - rewrite !length_app; specialize (IHf n); specialize (IHg (next (tseitin f n))).
    unfold andGate; simpl length; lia.
  - rewrite !length_app; specialize (IHf n); specialize (IHg (next (tseitin f n))).
    unfold orGate; simpl length; lia.
Qed.

(* Every Tseitin clause has at most three literals. *)
Theorem tseitin_width : forall f n c, In c (cls (tseitin f n)) -> length c <= 3.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n c Hc; simpl in Hc.
  - destruct Hc.
  - apply in_app_iff in Hc; destruct Hc as [Hc | Hc]; [eapply IH; exact Hc |].
    unfold negGate in Hc; simpl in Hc.
    destruct Hc as [<- | [<- | []]]; simpl; lia.
  - apply in_app_iff in Hc; destruct Hc as [Hc | Hc].
    + apply in_app_iff in Hc; destruct Hc as [Hc | Hc]; [eapply IHf; exact Hc | eapply IHg; exact Hc].
    + unfold andGate in Hc; simpl in Hc.
      destruct Hc as [<- | [<- | [<- | []]]]; simpl; lia.
  - apply in_app_iff in Hc; destruct Hc as [Hc | Hc].
    + apply in_app_iff in Hc; destruct Hc as [Hc | Hc]; [eapply IHf; exact Hc | eapply IHg; exact Hc].
    + unfold orGate in Hc; simpl in Hc.
      destruct Hc as [<- | [<- | [<- | []]]]; simpl; lia.
Qed.

(* Soundness. *)
Theorem tseitin_sound : forall f n b,
  evalCNF b (cls (tseitin f n)) = true -> b (out (tseitin f n)) = eval b f.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n b H; simpl in *.
  - reflexivity.
  - rewrite evalCNF_append in H; apply andb_prop in H; destruct H as [H1 H2].
    apply negGate_iff in H2; rewrite H2, (IH n b H1); reflexivity.
  - rewrite !evalCNF_append in H; apply andb_prop in H; destruct H as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H2].
    apply andGate_iff in H3; rewrite H3, (IHf n b H1), (IHg _ b H2); reflexivity.
  - rewrite !evalCNF_append in H; apply andb_prop in H; destruct H as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H2].
    apply orGate_iff in H3; rewrite H3, (IHf n b H1), (IHg _ b H2); reflexivity.
Qed.

(* Scope: when the inputs are below n, every variable used is below next. *)
Theorem tseitin_scope : forall f n, bound f <= n ->
  out (tseitin f n) < next (tseitin f n) /\
  forall v, In v (vars (cls (tseitin f n))) -> v < next (tseitin f n).
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n Hn; simpl in *.
  - split; [lia | intros v []].
  - destruct (IH n Hn) as [H1 H2]; split; [lia |].
    intros v Hv; rewrite vars_append in Hv; apply in_app_iff in Hv; destruct Hv as [Hv | Hv].
    + specialize (H2 v Hv); lia.
    + apply negGate_vars in Hv; lia.
  - pose proof (tseitin_next f n) as Er; pose proof (tseitin_next g (next (tseitin f n))) as Es.
    destruct (IHf n (max_le_l _ _ _ Hn)) as [H1 H2].
    destruct (IHg (next (tseitin f n))) as [H3 H4]; [pose proof (max_le_r _ _ _ Hn); lia |].
    split; [lia |].
    intros v Hv; rewrite !vars_append in Hv; apply in_app_iff in Hv; destruct Hv as [Hv | Hv].
    + apply in_app_iff in Hv; destruct Hv as [Hv | Hv].
      * specialize (H2 v Hv); lia.
      * specialize (H4 v Hv); lia.
    + apply andGate_vars in Hv; lia.
  - pose proof (tseitin_next f n) as Er; pose proof (tseitin_next g (next (tseitin f n))) as Es.
    destruct (IHf n (max_le_l _ _ _ Hn)) as [H1 H2].
    destruct (IHg (next (tseitin f n))) as [H3 H4]; [pose proof (max_le_r _ _ _ Hn); lia |].
    split; [lia |].
    intros v Hv; rewrite !vars_append in Hv; apply in_app_iff in Hv; destruct Hv as [Hv | Hv].
    + apply in_app_iff in Hv; destruct Hv as [Hv | Hv].
      * specialize (H2 v Hv); lia.
      * specialize (H4 v Hv); lia.
    + apply orGate_vars in Hv; lia.
Qed.

(* The canonical extension of an input assignment. *)
Fixpoint extend (f : Formula) (n : nat) (a : Assignment) : Assignment :=
  match f with
  | fvar _ => a
  | fneg f1 => update (extend f1 n a) (next (tseitin f1 n)) (negb (eval a f1))
  | fconj f1 f2 =>
      update (extend f2 (next (tseitin f1 n)) (extend f1 n a))
        (next (tseitin f2 (next (tseitin f1 n)))) (eval a f1 && eval a f2)
  | fdisj f1 f2 =>
      update (extend f2 (next (tseitin f1 n)) (extend f1 n a))
        (next (tseitin f2 (next (tseitin f1 n)))) (eval a f1 || eval a f2)
  end.

(* The extension does not touch variables below n. *)
Theorem extend_below : forall f n a v, v < n -> extend f n a v = a v.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n a v Hv; simpl.
  - reflexivity.
  - pose proof (tseitin_next f n).
    rewrite update_ne by lia; apply IH; exact Hv.
  - pose proof (tseitin_next f n); pose proof (tseitin_next g (next (tseitin f n))).
    rewrite update_ne by lia; rewrite IHg by lia; apply IHf; exact Hv.
  - pose proof (tseitin_next f n); pose proof (tseitin_next g (next (tseitin f n))).
    rewrite update_ne by lia; rewrite IHg by lia; apply IHf; exact Hv.
Qed.

(* Helper for binary gates. *)
Lemma extend_binary : forall f g n a val, bound f <= n -> bound g <= n ->
  evalCNF (extend f n a) (cls (tseitin f n)) = true /\
    extend f n a (out (tseitin f n)) = eval a f ->
  evalCNF (extend g (next (tseitin f n)) (extend f n a)) (cls (tseitin g (next (tseitin f n)))) = true /\
    extend g (next (tseitin f n)) (extend f n a) (out (tseitin g (next (tseitin f n)))) =
    eval (extend f n a) g ->
  let b := update (extend g (next (tseitin f n)) (extend f n a))
             (next (tseitin g (next (tseitin f n)))) val in
  evalCNF b (cls (tseitin f n) ++ cls (tseitin g (next (tseitin f n)))) = true /\
  b (out (tseitin f n)) = eval a f /\ b (out (tseitin g (next (tseitin f n)))) = eval a g.
Proof.
  intros f g n a val hf hg [c1 e1] [c2 e2] b.
  pose proof (tseitin_next f n) as hr.
  pose proof (tseitin_next g (next (tseitin f n))) as hs.
  destruct (tseitin_scope f n hf) as [o1 v1].
  destruct (tseitin_scope g (next (tseitin f n))) as [o2 v2]; [lia |].
  assert (hga : eval (extend f n a) g = eval a g).
  { apply formula_eval_congr; intros v Hv; apply extend_below; lia. }
  assert (b2r : evalCNF (extend g (next (tseitin f n)) (extend f n a)) (cls (tseitin f n)) = true).
  { rewrite <- c1; apply eval_congr; intros v Hv; apply extend_below; apply v1; exact Hv. }
  unfold b; split; [| split].
  - rewrite evalCNF_append, !update_evalCNF.
    + rewrite b2r, c2; reflexivity.
    + exact v2.
    + intros v Hv; specialize (v1 v Hv); lia.
  - rewrite update_ne by lia; rewrite extend_below by exact o1; exact e1.
  - rewrite update_ne by lia; rewrite e2; exact hga.
Qed.

(* Completeness. *)
Theorem extend_correct : forall f n a, bound f <= n ->
  evalCNF (extend f n a) (cls (tseitin f n)) = true /\
  extend f n a (out (tseitin f n)) = eval a f.
Proof.
  intros f; induction f as [i | f IH | f IHf g IHg | f IHf g IHg]; intros n a Hn; simpl in *.
  - split; reflexivity.
  - destruct (IH n a Hn) as [c1 e1]; destruct (tseitin_scope f n Hn) as [o1 v1].
    split; [| apply update_same].
    rewrite evalCNF_append, update_evalCNF by exact v1; rewrite c1; simpl.
    apply negGate_iff; rewrite update_same, update_ne by lia; rewrite e1; reflexivity.
  - pose proof (max_le_l _ _ _ Hn) as hf; pose proof (max_le_r _ _ _ Hn) as hg.
    pose proof (tseitin_next f n) as hr.
    destruct (extend_binary f g n a (eval a f && eval a g) hf hg (IHf n a hf)
      (IHg (next (tseitin f n)) (extend f n a) ltac:(lia))) as [c [e1 e2]].
    split; [| apply update_same].
    rewrite evalCNF_append, c; simpl.
    apply andGate_iff; rewrite update_same, e1, e2; reflexivity.
  - pose proof (max_le_l _ _ _ Hn) as hf; pose proof (max_le_r _ _ _ Hn) as hg.
    pose proof (tseitin_next f n) as hr.
    destruct (extend_binary f g n a (eval a f || eval a g) hf hg (IHf n a hf)
      (IHg (next (tseitin f n)) (extend f n a) ltac:(lia))) as [c [e1 e2]].
    split; [| apply update_same].
    rewrite evalCNF_append, c; simpl.
    apply orGate_iff; rewrite update_same, e1, e2; reflexivity.
Qed.

(* Tseitin equisatisfiability, for every formula. *)
Theorem tseitin_equisat : forall f,
  Satisfiable (tseitinCNF f) <-> exists a, eval a f = true.
Proof.
  intros f; split.
  - intros [b Hb]; unfold tseitinCNF in Hb; rewrite evalCNF_append in Hb.
    apply andb_prop in Hb; destruct Hb as [H1 H2].
    exists b; rewrite <- (tseitin_sound f _ b H1).
    destruct (b (out (tseitin f (bound f)))) eqn:E; [reflexivity |].
    simpl in H2; unfold evalLit, pl in H2; simpl in H2; rewrite E in H2; discriminate.
  - intros [a Ha]; destruct (extend_correct f (bound f) a (Nat.le_refl _)) as [c e].
    exists (extend f (bound f) a); unfold tseitinCNF; rewrite evalCNF_append, c; simpl.
    unfold evalLit, pl; simpl; rewrite e, Ha; reflexivity.
Qed.

(* Linear size: #clauses <= 3 * #gates + 1. *)
Theorem tseitinCNF_length : forall f, length (tseitinCNF f) <= 3 * gates f + 1.
Proof.
  intros f; unfold tseitinCNF; rewrite length_app; simpl length.
  pose proof (tseitin_length f (bound f)); lia.
Qed.

(* 3-CNF: every clause has at most three literals. *)
Theorem tseitinCNF_width : forall f c, In c (tseitinCNF f) -> length c <= 3.
Proof.
  intros f c Hc; unfold tseitinCNF in Hc; apply in_app_iff in Hc; destruct Hc as [Hc | Hc].
  - eapply tseitin_width; exact Hc.
  - destruct Hc as [<- | []]; simpl; lia.
Qed.

(* Count of variables: all variables are below bound f + gates f. *)
Theorem tseitinCNF_vars : forall f v, In v (vars (tseitinCNF f)) -> v < bound f + gates f.
Proof.
  intros f v Hv; destruct (tseitin_scope f (bound f) (Nat.le_refl _)) as [o h].
  pose proof (tseitin_next f (bound f)) as e.
  unfold tseitinCNF in Hv; rewrite vars_append in Hv; apply in_app_iff in Hv.
  destruct Hv as [Hv | Hv].
  - specialize (h v Hv); lia.
  - unfold pl in Hv; simpl in Hv; lia.
Qed.

(* Transfer (hardness preservation): circuit-SAT <= 3-SAT. *)
Theorem transfer : forall D : CNF -> bool,
  (forall phi : CNF, (forall c, In c phi -> length c <= 3) -> (D phi = true <-> Satisfiable phi)) ->
  forall f, D (tseitinCNF f) = true <-> exists a, eval a f = true.
Proof.
  intros D HD f; rewrite (HD _ (tseitinCNF_width f)); apply tseitin_equisat.
Qed.

(* Single definition: adding y <-> (x /\ z) for a fresh y preserves satisfiability. *)
Theorem define_and_sat_iff : forall phi y x z, ~ In y (vars phi) -> y <> x -> y <> z ->
  (Satisfiable (phi ++ andGate y x z) <-> Satisfiable phi).
Proof.
  intros phi y x z hy hx hz; split.
  - intros [b Hb]; rewrite evalCNF_append in Hb; apply andb_prop in Hb.
    exists b; apply Hb.
  - intros [a Ha]; exists (update a y (a x && a z)).
    assert (E : evalCNF (update a y (a x && a z)) phi = evalCNF a phi).
    { apply eval_congr; intros v Hv; apply update_ne; intros ->; contradiction. }
    rewrite evalCNF_append, E, Ha; simpl.
    apply andGate_iff; rewrite update_same, !update_ne by congruence; reflexivity.
Qed.

(* Extended resolution and the open obligation *)

Definition negLit (l : Lit) : Lit := mkLit (var l) (negb (pos l)).

Lemma evalLit_negLit : forall b l, evalLit b (negLit l) = negb (evalLit b l).
Proof. intros b [v p]; unfold evalLit, negLit; simpl; destruct p; simpl; [reflexivity | destruct (b v); reflexivity]. Qed.

Lemma evalLit_update : forall b y val l, var l <> y -> evalLit (update b y val) l = evalLit b l.
Proof. intros b y val l H; unfold evalLit; rewrite update_ne by exact H; reflexivity. Qed.

(* Extension clauses for y <-> (l1 /\ l2) with literals l1, l2. *)
Definition defGate (y : nat) (l1 l2 : Lit) : CNF :=
  [[nl y; l1]; [nl y; l2]; [pl y; negLit l1; negLit l2]].

Lemma defGate_iff : forall b y l1 l2,
  evalCNF b (defGate y l1 l2) = true <-> b y = (evalLit b l1 && evalLit b l2).
Proof.
  intros b y l1 l2; unfold defGate; simpl; rewrite !evalLit_negLit.
  unfold evalLit at 1 3 5, pl, nl; simpl.
  destruct (b y), (evalLit b l1), (evalLit b l2); simpl; split; intros; congruence.
Qed.

Lemma andGate_eq_defGate : forall y x z, andGate y x z = defGate y (pl x) (pl z).
Proof. reflexivity. Qed.

Inductive ERDerives (phi : CNF) : CNF -> Prop :=
| er_start : ERDerives phi phi
| er_res : forall pi c1 c2 c v, ERDerives phi pi -> In c1 pi -> In c2 pi ->
    (forall l, In l c1 -> l <> pl v -> In l c) ->
    (forall l, In l c2 -> l <> nl v -> In l c) ->
    ERDerives phi (c :: pi)
| er_ext : forall pi y l1 l2, ERDerives phi pi -> ~ In y (vars pi) ->
    var l1 <> y -> var l2 <> y ->
    ERDerives phi (defGate y l1 l2 ++ pi).

(* Soundness of extended resolution. *)
Theorem er_sat : forall phi pi, ERDerives phi pi -> Satisfiable phi -> Satisfiable pi.
Proof.
  intros phi pi H Hs; induction H as [| pi c1 c2 c v H IH h1 h2 k1 k2 | pi y l1 l2 H IH hy h1 h2].
  - exact Hs.
  - destruct IH as [b Hb]; exists b; simpl; rewrite Hb, andb_true_r.
    pose proof (proj1 (evalCNF_iff b pi) Hb) as Hall.
    destruct (b v) eqn:Hv.
    + destruct (proj1 (evalClause_iff b c2) (Hall c2 h2)) as [l [Hl He]].
      apply evalClause_iff; exists l; split; [| exact He].
      apply k2; [exact Hl |]; intros E; subst l.
      unfold nl, evalLit in He; simpl in He; rewrite Hv in He; discriminate.
    + destruct (proj1 (evalClause_iff b c1) (Hall c1 h1)) as [l [Hl He]].
      apply evalClause_iff; exists l; split; [| exact He].
      apply k1; [exact Hl |]; intros E; subst l.
      unfold pl, evalLit in He; simpl in He; rewrite Hv in He; discriminate.
  - destruct IH as [b Hb]; exists (update b y (evalLit b l1 && evalLit b l2)).
    assert (E : evalCNF (update b y (evalLit b l1 && evalLit b l2)) pi = evalCNF b pi).
    { apply eval_congr; intros w Hw; apply update_ne; intros ->; contradiction. }
    rewrite evalCNF_append, E, Hb, andb_true_r.
    apply defGate_iff; rewrite update_same, !evalLit_update by assumption; reflexivity.
Qed.

(* Extended resolution is sound. *)
Theorem er_sound : forall phi pi, ERDerives phi pi -> In [] pi -> ~ Satisfiable phi.
Proof.
  intros phi pi H Hin Hs; destruct (er_sat phi pi H Hs) as [b Hb].
  pose proof (proj1 (evalCNF_iff b pi) Hb [] Hin) as He; simpl in He; discriminate.
Qed.

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => length c + 1 + size phi'
  end.

(* Open obligation: a family of unsatisfiable CNFs with superpolynomial
   extended-resolution refutations. Not known (Cook-Reckhow 1979). *)
Definition ERSuperpolyLowerBound (family : nat -> CNF) : Prop :=
  (forall n, ~ Satisfiable (family n)) /\
  forall c k : nat, exists n, forall pi, ERDerives (family n) pi -> In [] pi ->
    c * (size (family n) + 1) ^ k < length pi.

Theorem obligation_excludes_poly_bound : forall family,
  ERSuperpolyLowerBound family -> forall c k,
  ~ (forall n, exists pi, ERDerives (family n) pi /\ In [] pi /\
       length pi <= c * (size (family n) + 1) ^ k).
Proof.
  intros family [_ H] c k Hall; destruct (H c k) as [n Hn].
  destruct (Hall n) as [pi [Hpi [He Hl]]]; specialize (Hn pi Hpi He); lia.
Qed.
