(* Issue #532, Idea 27: variable elimination (Davis-Putnam resolution).

   Verdict: refuted as a route (general theorem): elimination is exact for
   every CNF, but the clause count can grow multiplicatively at each step.

   Same content as ../lean/Idea27.lean:
   - eliminate_sat_iff (Davis-Putnam theorem, unconditional: clauses that are
     tautological in v are dropped);
   - eliminate_no_v: the result does not mention v;
   - eliminate_length: |eliminate v phi| = |rest| + |pos| * |neg|;
   - blowup_length / blowup_resolvent: p + q clauses become exactly p * q.
   See ../ideas/Idea27.md. *)

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

(* Davis-Putnam elimination *)

Definition hasLit (v : nat) (b : bool) (c : Clause) : bool :=
  existsb (fun l => Nat.eqb (var l) v && Bool.eqb (pos l) b) c.

Definition mentions (v : nat) (c : Clause) : bool :=
  existsb (fun l => Nat.eqb (var l) v) c.

Definition isPos (v : nat) (c : Clause) : bool := hasLit v true c && negb (hasLit v false c).
Definition isNeg (v : nat) (c : Clause) : bool := hasLit v false c && negb (hasLit v true c).

Definition strip (v : nat) (c : Clause) : Clause :=
  filter (fun l => negb (Nat.eqb (var l) v)) c.

Definition resolvent (v : nat) (c d : Clause) : Clause := strip v c ++ strip v d.

Definition posClauses (v : nat) (phi : CNF) : CNF := filter (isPos v) phi.
Definition negClauses (v : nat) (phi : CNF) : CNF := filter (isNeg v) phi.
Definition restClauses (v : nat) (phi : CNF) : CNF :=
  filter (fun c => negb (mentions v c)) phi.

Definition eliminate (v : nat) (phi : CNF) : CNF :=
  restClauses v phi ++
  flat_map (fun c => map (resolvent v c) (negClauses v phi)) (posClauses v phi).

Lemma hasLit_iff : forall v b c, hasLit v b c = true <-> In (mkLit v b) c.
Proof.
  intros v b c; unfold hasLit; rewrite existsb_exists; split.
  - intros [[w b'] [Hin H]]; simpl in H; apply andb_prop in H; destruct H as [H1 H2].
    apply Nat.eqb_eq in H1; apply eqb_prop in H2; subst; exact Hin.
  - intros Hin; exists (mkLit v b); split; [exact Hin |]; simpl.
    rewrite Nat.eqb_refl, eqb_reflx; reflexivity.
Qed.

Lemma mentions_iff : forall v c, mentions v c = true <-> exists l, In l c /\ var l = v.
Proof.
  intros v c; unfold mentions; rewrite existsb_exists; split;
    intros [l [Hin H]]; exists l; split; try exact Hin; apply Nat.eqb_eq; exact H.
Qed.

Lemma mentions_cases : forall v c, mentions v c = true ->
  hasLit v true c = true \/ hasLit v false c = true.
Proof.
  intros v c H; apply mentions_iff in H; destruct H as [[w b] [Hin Hw]]; simpl in Hw; subst.
  destruct b; [left | right]; apply hasLit_iff; exact Hin.
Qed.

Lemma mem_strip : forall v c l, In l (strip v c) <-> In l c /\ var l <> v.
Proof.
  intros v c l; unfold strip; rewrite filter_In, negb_true_iff, Nat.eqb_neq; tauto.
Qed.

Lemma evalClause_append : forall a (c d : Clause),
  evalClause a (c ++ d) = evalClause a c || evalClause a d.
Proof.
  intros a c d; induction c as [|l c IH]; simpl; [reflexivity | rewrite IH, orb_assoc; reflexivity].
Qed.

(* No clause of the eliminated formula mentions v. *)
Theorem eliminate_no_v : forall v phi c, In c (eliminate v phi) -> mentions v c = false.
Proof.
  intros v phi c Hc; unfold eliminate in Hc; apply in_app_iff in Hc.
  destruct Hc as [Hc | Hc].
  - unfold restClauses in Hc; apply filter_In in Hc; destruct Hc as [_ H].
    apply negb_true_iff; exact H.
  - apply in_flat_map in Hc; destruct Hc as [c1 [_ Hc]].
    apply in_map_iff in Hc; destruct Hc as [d [Heq _]]; subst c.
    destruct (mentions v (resolvent v c1 d)) eqn:Hm; [| reflexivity].
    apply mentions_iff in Hm; destruct Hm as [l [Hl Hv]].
    unfold resolvent in Hl; apply in_app_iff in Hl.
    destruct Hl as [Hl | Hl]; apply mem_strip in Hl; destruct Hl as [_ Hl]; contradiction.
Qed.

(* Exact size of one elimination step. *)
Theorem eliminate_length : forall v phi,
  length (eliminate v phi) =
  length (restClauses v phi) + length (posClauses v phi) * length (negClauses v phi).
Proof.
  intros v phi; unfold eliminate; rewrite length_app; f_equal.
  induction (posClauses v phi) as [|c P IH]; simpl; [reflexivity |].
  rewrite length_app, length_map, IH; reflexivity.
Qed.

(* Soundness direction. *)
Theorem eliminate_sound : forall v phi a,
  evalCNF a phi = true -> evalCNF a (eliminate v phi) = true.
Proof.
  intros v phi a Ha; rewrite evalCNF_iff in Ha |- *; intros c Hc.
  unfold eliminate in Hc; apply in_app_iff in Hc; destruct Hc as [Hc | Hc].
  - unfold restClauses in Hc; apply filter_In in Hc; apply Ha; apply Hc.
  - apply in_flat_map in Hc; destruct Hc as [c1 [Hc1 Hc]].
    apply in_map_iff in Hc; destruct Hc as [d [Heq Hd]]; subst c.
    unfold posClauses in Hc1; apply filter_In in Hc1; destruct Hc1 as [Hc1 Hp].
    unfold negClauses in Hd; apply filter_In in Hd; destruct Hd as [Hd Hn].
    unfold isPos in Hp; unfold isNeg in Hn.
    apply andb_prop in Hp; destruct Hp as [_ Hp]; apply negb_true_iff in Hp.
    apply andb_prop in Hn; destruct Hn as [_ Hn]; apply negb_true_iff in Hn.
    unfold resolvent; rewrite evalClause_append; apply orb_true_iff.
    destruct (a v) eqn:Hav.
    + right. destruct (proj1 (evalClause_iff a d) (Ha d Hd)) as [[w b] [Hl Hle]].
      apply evalClause_iff; exists (mkLit w b); split; [| exact Hle].
      apply mem_strip; split; [exact Hl | simpl; intros Hw; subst w].
      destruct b.
      * apply hasLit_iff in Hl; rewrite Hl in Hn; discriminate.
      * unfold evalLit in Hle; simpl in Hle; rewrite Hav in Hle; discriminate.
    + left. destruct (proj1 (evalClause_iff a c1) (Ha c1 Hc1)) as [[w b] [Hl Hle]].
      apply evalClause_iff; exists (mkLit w b); split; [| exact Hle].
      apply mem_strip; split; [exact Hl | simpl; intros Hw; subst w].
      destruct b.
      * unfold evalLit in Hle; simpl in Hle; rewrite Hav in Hle; discriminate.
      * apply hasLit_iff in Hl; rewrite Hl in Hp; discriminate.
Qed.

Definition chooseVal (v : nat) (phi : CNF) (b : Assignment) : bool :=
  negb (forallb (fun c => evalClause b (strip v c)) (posClauses v phi)).

Definition update (b : Assignment) (v : nat) (val : bool) : Assignment :=
  fun w => if Nat.eq_dec w v then val else b w.

Lemma update_strip : forall b v val c,
  evalClause (update b v val) (strip v c) = evalClause b (strip v c).
Proof.
  intros b v val c; apply evalClause_congr; intros w Hw.
  unfold clauseVars in Hw; apply in_map_iff in Hw; destruct Hw as [l [Hw Hl]]; subst w.
  apply mem_strip in Hl; destruct Hl as [_ Hl]; unfold update.
  destruct (Nat.eq_dec (var l) v); [contradiction | reflexivity].
Qed.

Lemma update_nomention : forall b v val c, mentions v c = false ->
  evalClause (update b v val) c = evalClause b c.
Proof.
  intros b v val c H; apply evalClause_congr; intros w Hw.
  unfold clauseVars in Hw; apply in_map_iff in Hw; destruct Hw as [l [Hw Hl]]; subst w.
  unfold update; destruct (Nat.eq_dec (var l) v) as [E|]; [| reflexivity].
  assert (M : mentions v c = true) by (apply mentions_iff; exists l; auto).
  rewrite H in M; discriminate.
Qed.

Lemma sat_of_strip : forall a v c,
  evalClause a (strip v c) = true -> evalClause a c = true.
Proof.
  intros a v c H; apply evalClause_iff in H; destruct H as [l [Hl Hle]].
  apply evalClause_iff; exists l; split; [apply mem_strip in Hl; apply Hl | exact Hle].
Qed.

Lemma sat_of_lit : forall b v val c, hasLit v val c = true ->
  evalClause (update b v val) c = true.
Proof.
  intros b v val c H; apply evalClause_iff; exists (mkLit v val); split.
  - apply hasLit_iff; exact H.
  - unfold evalLit, update; simpl.
    destruct (Nat.eq_dec v v) as [_|n]; [| contradiction].
    destruct val; reflexivity.
Qed.

(* Completeness direction. *)
Theorem eliminate_complete : forall v phi b,
  evalCNF b (eliminate v phi) = true ->
  evalCNF (update b v (chooseVal v phi b)) phi = true.
Proof.
  intros v phi b Hb; rewrite evalCNF_iff in Hb |- *; intros c Hc.
  destruct (mentions v c) eqn:Hm.
  - destruct (hasLit v true c) eqn:Hp; destruct (hasLit v false c) eqn:Hn.
    + (* tautological in v *)
      destruct (chooseVal v phi b); apply sat_of_lit; assumption.
    + (* positive clause *)
      destruct (chooseVal v phi b) eqn:Hval.
      * apply sat_of_lit; exact Hp.
      * unfold chooseVal in Hval; apply negb_false_iff in Hval.
        rewrite forallb_forall in Hval.
        apply sat_of_strip with (v := v); rewrite update_strip; apply Hval.
        unfold posClauses; apply filter_In; split; [exact Hc |].
        unfold isPos; rewrite Hp, Hn; reflexivity.
    + (* negative clause *)
      destruct (chooseVal v phi b) eqn:Hval.
      * unfold chooseVal in Hval; apply negb_true_iff in Hval.
        destruct (forallb (fun c0 => evalClause b (strip v c0)) (posClauses v phi)) eqn:Hall;
          [discriminate |].
        assert (Ex : exists c0, In c0 (posClauses v phi) /\ evalClause b (strip v c0) = false).
        { clear -Hall. induction (posClauses v phi) as [|c0 P IH]; simpl in Hall; [discriminate |].
          destruct (evalClause b (strip v c0)) eqn:E; simpl in Hall.
          - destruct (IH Hall) as [c1 [H1 H2]]; exists c1; split; [right; exact H1 | exact H2].
          - exists c0; split; [left; reflexivity | exact E]. }
        destruct Ex as [c0 [Hc0 Hc0f]].
        assert (Hres : evalClause b (resolvent v c0 c) = true).
        { apply Hb; unfold eliminate; apply in_app_iff; right.
          apply in_flat_map; exists c0; split; [exact Hc0 |].
          apply in_map_iff; exists c; split; [reflexivity |].
          unfold negClauses; apply filter_In; split; [exact Hc |].
          unfold isNeg; rewrite Hp, Hn; reflexivity. }
        unfold resolvent in Hres; rewrite evalClause_append, Hc0f in Hres; simpl in Hres.
        apply sat_of_strip with (v := v); rewrite update_strip; exact Hres.
      * apply sat_of_lit; exact Hn.
    + destruct (mentions_cases v c Hm) as [H | H]; rewrite H in *; discriminate.
  - rewrite update_nomention by exact Hm.
    apply Hb; unfold eliminate; apply in_app_iff; left.
    unfold restClauses; apply filter_In; split; [exact Hc | rewrite Hm; reflexivity].
Qed.

(* Davis-Putnam theorem. *)
Theorem eliminate_sat_iff : forall v phi,
  Satisfiable phi <-> Satisfiable (eliminate v phi).
Proof.
  intros v phi; split.
  - intros [a Ha]; exists a; apply eliminate_sound; exact Ha.
  - intros [b Hb]; exists (update b v (chooseVal v phi b)); apply eliminate_complete; exact Hb.
Qed.

(* Multiplicative blow-up *)

Definition posSide (p : nat) : CNF :=
  map (fun i => [mkLit 0 true; mkLit (S i) true]) (seq 0 p).

(* The side variable of the j-th negative clause is x_{p+1+j} = S (p + j). *)
Definition negSide (p q : nat) : CNF :=
  map (fun j => [mkLit 0 false; mkLit (S (p + j)) true]) (seq 0 q).

Definition blowup (p q : nat) : CNF := posSide p ++ negSide p q.

Theorem blowup_clauses : forall p q, length (blowup p q) = p + q.
Proof.
  intros p q; unfold blowup, posSide, negSide.
  rewrite length_app, !length_map, !length_seq; reflexivity.
Qed.

Lemma filter_all : forall (A : Type) (f : A -> bool) l,
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l; induction l as [|x l IH]; intros H; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity |].
  intros y Hy; apply H; right; exact Hy.
Qed.

Lemma filter_none : forall (A : Type) (f : A -> bool) l,
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros A f l; induction l as [|x l IH]; intros H; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity |].
  intros y Hy; apply H; right; exact Hy.
Qed.

Lemma posClauses_blowup : forall p q, posClauses 0 (blowup p q) = posSide p.
Proof.
  intros p q; unfold posClauses, blowup; rewrite filter_app.
  rewrite filter_all, filter_none, app_nil_r; [reflexivity | |].
  - intros c Hc; unfold negSide in Hc; apply in_map_iff in Hc.
    destruct Hc as [j [Hj _]]; subst c; reflexivity.
  - intros c Hc; unfold posSide in Hc; apply in_map_iff in Hc.
    destruct Hc as [i [Hi _]]; subst c; reflexivity.
Qed.

Lemma negClauses_blowup : forall p q, negClauses 0 (blowup p q) = negSide p q.
Proof.
  intros p q; unfold negClauses, blowup; rewrite filter_app.
  rewrite filter_none, filter_all; [reflexivity | |].
  - intros c Hc; unfold negSide in Hc; apply in_map_iff in Hc.
    destruct Hc as [j [Hj _]]; subst c; reflexivity.
  - intros c Hc; unfold posSide in Hc; apply in_map_iff in Hc.
    destruct Hc as [i [Hi _]]; subst c; reflexivity.
Qed.

Lemma restClauses_blowup : forall p q, restClauses 0 (blowup p q) = [].
Proof.
  intros p q; unfold restClauses; apply filter_none; intros c Hc.
  unfold blowup in Hc; apply in_app_iff in Hc; destruct Hc as [Hc | Hc].
  - unfold posSide in Hc; apply in_map_iff in Hc; destruct Hc as [i [Hi _]]; subst c; reflexivity.
  - unfold negSide in Hc; apply in_map_iff in Hc; destruct Hc as [j [Hj _]]; subst c; reflexivity.
Qed.

(* Blow-up: p + q clauses become exactly p * q. *)
Theorem blowup_length : forall p q, length (eliminate 0 (blowup p q)) = p * q.
Proof.
  intros p q; rewrite eliminate_length, posClauses_blowup, negClauses_blowup, restClauses_blowup.
  unfold posSide, negSide; rewrite !length_map, !length_seq; reflexivity.
Qed.

Theorem blowup_resolvent : forall p i j,
  resolvent 0 [mkLit 0 true; mkLit (S i) true] [mkLit 0 false; mkLit (S (p + j)) true] =
  [mkLit (S i) true; mkLit (S (p + j)) true].
Proof. intros; reflexivity. Qed.
