(* Issue #532, Idea 26: separator consistency.

   Verdict: refuted as a route (general theorem): separator decomposition is
   exact only when all 2^|S| separator states are tracked, and no summary
   with fewer states is sound in general.

   Same content as ../lean/Idea26.lean:
   - separator_sat_iff: A ++ B (shared variables inside S) is satisfiable iff
     some state sigma in allBool |S| is realised by a model of A and by a
     model of B;
   - length_allBool / mem_allBool: 2^n states, all vectors of length n;
   - separate_not_joint: [[x]] and [[~x]] separately but not jointly SAT;
   - compatible_states_units / equality_gadget: unit formulas force exactly
     one separator state; the union is SAT iff the states are equal;
   - summary_must_be_injective: a sound summary distinguishes all states.
   See ../ideas/Idea26.md. *)

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

(* Separator states *)

Fixpoint allBool (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allBool n') ++ map (cons true) (allBool n')
  end.

Theorem length_allBool : forall n, length (allBool n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite length_app, !length_map, IH; lia.
Qed.

Theorem mem_allBool : forall n (sigma : list bool),
  In sigma (allBool n) <-> length sigma = n.
Proof.
  induction n as [|n IH]; intros sigma; simpl.
  - split.
    + intros [H | []]; subst; reflexivity.
    + destruct sigma; simpl; [intros _; left; reflexivity | discriminate].
  - rewrite in_app_iff, !in_map_iff; split.
    + intros [[t [Ht Hin]] | [t [Ht Hin]]]; subst; simpl; f_equal; apply IH; exact Hin.
    + destruct sigma as [|b sigma]; simpl; [discriminate |].
      intros Hlen; injection Hlen as Hlen.
      destruct b; [right | left]; exists sigma; split; try reflexivity; apply IH; exact Hlen.
Qed.

Definition restrict (S : list nat) (a : Assignment) : list bool := map a S.

Lemma restrict_length : forall S a, length (restrict S a) = length S.
Proof. intros; unfold restrict; apply length_map. Qed.

Lemma restrict_eq_agree : forall S (a b : Assignment),
  restrict S a = restrict S b -> forall v, In v S -> a v = b v.
Proof.
  unfold restrict; induction S as [|s S IH]; intros a b H v Hv; simpl in *.
  - contradiction.
  - injection H as H1 H2. destruct Hv as [Hv | Hv].
    + subst; exact H1.
    + exact (IH a b H2 v Hv).
Qed.

(* Separator theorem. *)
Theorem separator_sat_iff : forall (A B : CNF) (S : list nat),
  (forall v, In v (vars A) -> In v (vars B) -> In v S) ->
  (Satisfiable (A ++ B) <->
   exists sigma, In sigma (allBool (length S)) /\
     (exists a, restrict S a = sigma /\ evalCNF a A = true) /\
     (exists b, restrict S b = sigma /\ evalCNF b B = true)).
Proof.
  intros A B S HS; split.
  - intros [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
    destruct Ha as [HA HB].
    exists (restrict S a); split.
    + apply mem_allBool, restrict_length.
    + split; exists a; split; auto.
  - intros [sigma [_ [[a [Has Ha]] [b [Hbs Hb]]]]].
    assert (agree : forall v, In v S -> a v = b v).
    { apply restrict_eq_agree; rewrite Has, Hbs; reflexivity. }
    set (c := fun v => if in_dec Nat.eq_dec v (vars A) then a v else b v).
    exists c; rewrite evalCNF_append.
    assert (HcA : evalCNF c A = evalCNF a A).
    { apply eval_congr; intros v Hv; unfold c.
      destruct (in_dec Nat.eq_dec v (vars A)); [reflexivity | contradiction]. }
    assert (HcB : evalCNF c B = evalCNF b B).
    { apply eval_congr; intros v Hv; unfold c.
      destruct (in_dec Nat.eq_dec v (vars A)) as [HvA|HvA].
      - apply agree, HS; assumption.
      - reflexivity. }
    rewrite HcA, HcB, Ha, Hb; reflexivity.
Qed.

(* Countermodel family, |S| = 1. *)
Theorem separate_not_joint : forall x : nat,
  Satisfiable [[mkLit x true]] /\ Satisfiable [[mkLit x false]] /\
  ~ Satisfiable ([[mkLit x true]] ++ [[mkLit x false]]).
Proof.
  intros x; split; [exists (fun _ => true); reflexivity |].
  split; [exists (fun _ => false); reflexivity |].
  intros [a Ha]; simpl in Ha; unfold evalLit in Ha; simpl in Ha.
  destruct (a x); discriminate.
Qed.

(* The equality gadget *)

Fixpoint units (S : list nat) (sigma : list bool) : CNF :=
  match S, sigma with
  | s :: S', b :: sigma' => [mkLit s b] :: units S' sigma'
  | _, _ => []
  end.

Lemma evalLit_unit : forall (a : Assignment) s b,
  evalLit a (mkLit s b) = true <-> a s = b.
Proof.
  intros a s b; unfold evalLit; simpl.
  destruct b, (a s); simpl; split; intros H; try reflexivity; discriminate.
Qed.

Lemma units_eval : forall (a : Assignment) S (sigma : list bool),
  length sigma = length S ->
  (evalCNF a (units S sigma) = true <-> restrict S a = sigma).
Proof.
  intros a S; unfold restrict; induction S as [|s S IH]; intros sigma Hlen;
    destruct sigma as [|b sigma]; simpl in *; try discriminate.
  - split; reflexivity.
  - injection Hlen as Hlen.
    rewrite orb_false_r; split.
    + intros H; apply andb_prop in H; destruct H as [H1 H2].
      apply evalLit_unit in H1; apply (IH sigma Hlen) in H2.
      rewrite H1, H2; reflexivity.
    + intros H; injection H as H1 H2.
      apply andb_true_intro; split.
      * apply evalLit_unit; exact H1.
      * apply (IH sigma Hlen); exact H2.
Qed.

Theorem realizable : forall S, NoDup S -> forall sigma : list bool,
  length sigma = length S -> exists a, restrict S a = sigma.
Proof.
  unfold restrict; induction S as [|s S IH]; intros HS sigma Hlen;
    destruct sigma as [|b sigma]; simpl in *; try discriminate.
  - exists (fun _ => false); reflexivity.
  - injection Hlen as Hlen.
    inversion HS as [|s' S' Hs HS']; subst.
    destruct (IH HS' sigma Hlen) as [a Ha].
    exists (fun v => if Nat.eq_dec v s then b else a v).
    destruct (Nat.eq_dec s s) as [_|Hne]; [| contradiction].
    f_equal. rewrite <- Ha. apply map_ext_in. intros v Hv.
    destruct (Nat.eq_dec v s) as [Heq|_]; [subst; contradiction | reflexivity].
Qed.

(* Compatibility sets are singletons. *)
Theorem compatible_states_units : forall S, NoDup S -> forall sigma tau : list bool,
  length sigma = length S ->
  ((exists a, restrict S a = tau /\ evalCNF a (units S sigma) = true) <-> tau = sigma).
Proof.
  intros S HS sigma tau Hs; split.
  - intros [a [Hat Ha]]; rewrite <- Hat; apply (units_eval a S sigma Hs); exact Ha.
  - intros H; subst tau.
    destruct (realizable S HS sigma Hs) as [a Ha].
    exists a; split; [exact Ha | apply (units_eval a S sigma Hs); exact Ha].
Qed.

(* Equality gadget. *)
Theorem equality_gadget : forall S, NoDup S -> forall sigma tau : list bool,
  length sigma = length S -> length tau = length S ->
  Satisfiable (units S sigma) /\ Satisfiable (units S tau) /\
  (Satisfiable (units S sigma ++ units S tau) <-> sigma = tau).
Proof.
  intros S HS sigma tau Hs Ht; split; [| split].
  - destruct (realizable S HS sigma Hs) as [a Ha].
    exists a; apply (units_eval a S sigma Hs); exact Ha.
  - destruct (realizable S HS tau Ht) as [a Ha].
    exists a; apply (units_eval a S tau Ht); exact Ha.
  - split.
    + intros [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
      destruct Ha as [H1 H2].
      apply (units_eval a S sigma Hs) in H1; apply (units_eval a S tau Ht) in H2.
      rewrite <- H1, <- H2; reflexivity.
    + intros H; subst tau.
      destruct (realizable S HS sigma Hs) as [a Ha].
      exists a; rewrite evalCNF_append.
      assert (E : evalCNF a (units S sigma) = true) by (apply (units_eval a S sigma Hs); exact Ha).
      rewrite E; reflexivity.
Qed.

(* No lossy summary. *)
Theorem summary_must_be_injective : forall (beta : Type) S, NoDup S ->
  forall (summ : list bool -> beta) (D : beta -> list bool -> bool),
  (forall sigma tau, length sigma = length S -> length tau = length S ->
     (D (summ sigma) tau = true <-> Satisfiable (units S sigma ++ units S tau))) ->
  forall sigma tau, length sigma = length S -> length tau = length S ->
  summ sigma = summ tau -> sigma = tau.
Proof.
  intros beta S HS summ D HD sigma tau Hs Ht Hsum.
  assert (H1 : D (summ sigma) sigma = true).
  { apply (HD sigma sigma Hs Hs).
    apply (equality_gadget S HS sigma sigma Hs Hs); reflexivity. }
  rewrite Hsum in H1.
  apply (HD tau sigma Ht Hs) in H1.
  apply (equality_gadget S HS tau sigma Ht Hs) in H1.
  symmetry; exact H1.
Qed.

(* The open obligation (Sep), one level: a map in the class PolyTime sending
   every CNF to an equisatisfiable split A ++ B whose shared variables lie in a
   separator Sep (a list of variables) of length at most w |phi|. *)
Definition SeparatorObligation (PolyTime : (CNF -> CNF * CNF * list nat) -> Prop)
  (w : nat -> nat) : Prop :=
  exists f : CNF -> CNF * CNF * list nat, PolyTime f /\ forall phi,
    let '(A, B, Sep) := f phi in
    (forall v, In v (vars A) -> In v (vars B) -> In v Sep) /\
    length Sep <= w (length phi) /\
    (Satisfiable phi <-> Satisfiable (A ++ B)).

(* Conditional theorem: under the obligation, satisfiability of every CNF is
   decided by the 2 ^ w(|phi|) separator states. *)
Theorem separator_obligation_states (PolyTime : (CNF -> CNF * CNF * list nat) -> Prop)
  (w : nat -> nat) :
  SeparatorObligation PolyTime w ->
  exists f : CNF -> CNF * CNF * list nat, PolyTime f /\ forall phi,
    let '(A, B, Sep) := f phi in
    length Sep <= w (length phi) /\
    (Satisfiable phi <-> exists sigma, In sigma (allBool (length Sep)) /\
      (exists a, restrict Sep a = sigma /\ evalCNF a A = true) /\
      (exists b, restrict Sep b = sigma /\ evalCNF b B = true)).
Proof.
  intros (f & hf & hall). exists f. split; [exact hf|]. intro phi.
  specialize (hall phi). destruct (f phi) as [[A B] Sep].
  destruct hall as (hSep & hw & hp). split; [exact hw|].
  rewrite hp. apply separator_sat_iff. exact hSep.
Qed.
