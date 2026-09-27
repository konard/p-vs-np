(* Issue #532, Idea 10: monotone lower bounds and transfer to general circuits.

   Rocq counterpart of lean/Idea10.lean; theorem names are aligned.

   Boolean formulas over AND/OR/NOT with variables and literals, evaluated
   on assignments nat -> bool.  A formula is monotone when it has no NOT.
   Proved for all formulas, assignments and n:
   - monotone_eval: monotone formulas compute monotone functions;
   - no_monotone_formula_for_not / no_monotone_formula_for_parity: no
     monotone formula of any size computes ~x0, or parity of n >= 2
     variables, while parityCirc_correct gives general formulas for parity;
   - monotone_complete: every monotone function of the first n variables
     has a monotone formula (lower bounds are about size, not expressibility);
   - doubleRail_correct, undual_correct, general_iff_double_rail: a general
     superpolynomial formula lower bound is EQUIVALENT to a monotone lower
     bound for the double-rail partial function (correct only on consistent
     inputs (x, ~x)), not implied by a monotone bound for f itself.

   Tie to the shared machine model.  The lower-bound shapes are schemas over
   a formula family (GeneralSuperpolyLowerBoundFor,
   MonotoneSuperpolyLowerBoundFor, DoubleRailLowerBoundFor).  They are
   instantiated on the language SAT of Machines.v through [slice SAT n] of
   Circuits.v, the Boolean function SAT computes on inputs of length n:
   - SATFormulaLowerBound (open obligation): SAT has no polynomial-size
     formulas; NPNotInPolyFormulas (open obligation): some InNP language has
     none;
   - npNotInPolyFormulas_of_sat: with SATInNP the first gives the second.
     This does not give P <> NP: that would also need PSubsetPolyFormulas
     (a P in NC1-type statement, open and widely believed false), as
     pNotEqualsNP_of_satFormulaLowerBound makes explicit;
   - sat_slice_not_monotone, sat_monotone_lower_bound_trivial: SAT on words
     is not monotone at length 2, so the monotone lower bound for SAT holds
     for a trivial reason;
   - const_no_general_lower_bound: the lower-bound shape fails for a
     constant family, so it is not vacuously true.

   Verdict: "monotone lower bound for an NP function => P <> NP" is refuted
   in full strength by Tardos (1988) (not formalized).  The remaining
   obligation SATFormulaLowerBound is open.  Nothing here proves or refutes
   P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.

Inductive Circ : Type :=
  | Var : nat -> Circ
  | Lit : bool -> Circ
  | Conj : Circ -> Circ -> Circ
  | Disj : Circ -> Circ -> Circ
  | Neg : Circ -> Circ.

Fixpoint eval (c : Circ) (x : nat -> bool) : bool :=
  match c with
  | Var i => x i
  | Lit b => b
  | Conj a b => eval a x && eval b x
  | Disj a b => eval a x || eval b x
  | Neg a => negb (eval a x)
  end.

(** Number of nodes. *)
Fixpoint size (c : Circ) : nat :=
  match c with
  | Var _ => 1
  | Lit _ => 1
  | Conj a b => size a + size b + 1
  | Disj a b => size a + size b + 1
  | Neg a => size a + 1
  end.

(** A formula is monotone if it contains no NOT gate. *)
Fixpoint notFree (c : Circ) : bool :=
  match c with
  | Var _ => true
  | Lit _ => true
  | Conj a b => notFree a && notFree b
  | Disj a b => notFree a && notFree b
  | Neg _ => false
  end.

(** Boolean order (false <= true). *)
Definition leB (a b : bool) : bool := negb a || b.

Definition LeAssign (x y : nat -> bool) : Prop := forall i, leB (x i) (y i) = true.

Definition MonotoneFn (f : (nat -> bool) -> bool) : Prop :=
  forall x y, LeAssign x y -> leB (f x) (f y) = true.

Theorem leB_and : forall a b c d, leB a c = true -> leB b d = true ->
  leB (a && b) (c && d) = true.
Proof. intros [|] [|] [|] [|]; simpl; auto. Qed.

Theorem leB_or : forall a b c d, leB a c = true -> leB b d = true ->
  leB (a || b) (c || d) = true.
Proof. intros [|] [|] [|] [|]; simpl; auto. Qed.

(** Monotone formulas compute monotone functions. *)
Theorem monotone_eval : forall c, notFree c = true -> forall x y, LeAssign x y ->
  leB (eval c x) (eval c y) = true.
Proof.
  induction c as [i|b|a IHa b IHb|a IHa b IHb|a IHa]; intros hc x y hxy; simpl in *.
  - apply hxy.
  - destruct b; reflexivity.
  - apply andb_true_iff in hc as [h1 h2].
    apply leB_and; [apply IHa | apply IHb]; assumption.
  - apply andb_true_iff in hc as [h1 h2].
    apply leB_or; [apply IHa | apply IHb]; assumption.
  - discriminate.
Qed.

Theorem notFree_computes_monotone : forall c, notFree c = true -> MonotoneFn (eval c).
Proof. intros c hc x y h. apply monotone_eval; assumption. Qed.

(** Negation of x0 is not monotone. *)
Theorem neg_not_monotone : ~ MonotoneFn (fun x => negb (x 0)).
Proof.
  intro h.
  specialize (h (fun _ => false) (fun _ => true) (fun _ => eq_refl)).
  simpl in h. discriminate.
Qed.

(** No monotone formula, of any size, computes ~x0. *)
Theorem no_monotone_formula_for_not : forall c, notFree c = true ->
  ~ (forall x, eval c x = negb (x 0)).
Proof.
  intros c hc h. apply neg_not_monotone. intros x y hxy.
  pose proof (monotone_eval c hc x y hxy) as H.
  rewrite (h x), (h y) in H. exact H.
Qed.

(** Parity of the first n variables. *)
Fixpoint parity (n : nat) (x : nat -> bool) : bool :=
  match n with
  | 0 => false
  | S n => xorb (parity n x) (x n)
  end.

Theorem parity_first : forall n, 1 <= n -> parity n (fun i => Nat.eqb i 0) = true.
Proof.
  induction n as [|n IH]; intro hn; [lia|].
  simpl. destruct n as [|n].
  - reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

Theorem parity_two : forall n, 2 <= n -> parity n (fun i => Nat.ltb i 2) = false.
Proof.
  induction n as [|n IH]; intro hn; [lia|].
  simpl. destruct (Nat.eq_dec n 1) as [e|e].
  - subst n. reflexivity.
  - rewrite IH by lia.
    replace (Nat.ltb n 2) with false; [reflexivity|].
    symmetry. apply Nat.ltb_ge. lia.
Qed.

(** Parity of n >= 2 variables is not monotone. *)
Theorem parity_not_monotone : forall n, 2 <= n -> ~ MonotoneFn (parity n).
Proof.
  intros n hn h.
  assert (hle : LeAssign (fun i => Nat.eqb i 0) (fun i => Nat.ltb i 2)).
  { intro i. destruct i as [|[|i]]; reflexivity. }
  specialize (h _ _ hle).
  rewrite parity_first in h by lia. rewrite parity_two in h by lia.
  discriminate.
Qed.

(** No monotone formula computes parity of n >= 2 variables. *)
Theorem no_monotone_formula_for_parity : forall n, 2 <= n -> forall c, notFree c = true ->
  ~ (forall x, eval c x = parity n x).
Proof.
  intros n hn c hc h. apply (parity_not_monotone n hn). intros x y hxy.
  pose proof (monotone_eval c hc x y hxy) as H.
  rewrite (h x), (h y) in H. exact H.
Qed.

(** XOR from AND/OR/NOT. *)
Definition xorC (a b : Circ) : Circ := Disj (Conj a (Neg b)) (Conj (Neg a) b).

Fixpoint parityCirc (n : nat) : Circ :=
  match n with
  | 0 => Lit false
  | S n => xorC (parityCirc n) (Var n)
  end.

(** General formulas (with NOT) compute parity for every n. *)
Theorem parityCirc_correct : forall n x, eval (parityCirc n) x = parity n x.
Proof.
  induction n as [|n IH]; intro x; [reflexivity|].
  simpl. rewrite IH. destruct (parity n x), (x n); reflexivity.
Qed.

(** * Monotone completeness *)

Definition upd (x : nat -> bool) (k : nat) (b : bool) : nat -> bool :=
  fun i => if Nat.eqb i k then b else x i.

Definition DependsOn (f : (nat -> bool) -> bool) (n : nat) : Prop :=
  forall x y, (forall i, i < n -> x i = y i) -> f x = f y.

(** Shannon-style monotone formula: f = (x_n /\ f[x_n:=1]) \/ f[x_n:=0]. *)
Fixpoint build (n : nat) (f : (nat -> bool) -> bool) : Circ :=
  match n with
  | 0 => Lit (f (fun _ => false))
  | S n => Disj (Conj (Var n) (build n (fun x => f (upd x n true))))
                (build n (fun x => f (upd x n false)))
  end.

Theorem build_notFree : forall n f, notFree (build n f) = true.
Proof.
  induction n as [|n IH]; intro f; [reflexivity|].
  simpl. rewrite !IH. reflexivity.
Qed.

Theorem upd_le : forall x y k b, LeAssign x y -> LeAssign (upd x k b) (upd y k b).
Proof.
  intros x y k b h i. unfold upd.
  destruct (Nat.eqb i k); [destruct b; reflexivity | apply h].
Qed.

(** Monotone completeness: every monotone function depending only on the
    first n variables is computed by the monotone formula [build n f]. *)
Theorem monotone_complete : forall n f, MonotoneFn f -> DependsOn f n ->
  forall x, eval (build n f) x = f x.
Proof.
  induction n as [|n IH]; intros f hm hd x.
  - simpl. apply hd. intros i hi. lia.
  - assert (hm1 : forall b, MonotoneFn (fun x => f (upd x n b))).
    { intros b x' y' h. apply hm. apply upd_le. exact h. }
    assert (hdb : forall b, DependsOn (fun x => f (upd x n b)) n).
    { intros b x' y' hxy. apply hd. intros i hi. unfold upd.
      destruct (Nat.eqb_spec i n); [reflexivity|]. apply hxy. lia. }
    assert (hsame : forall b, x n = b -> f (upd x n b) = f x).
    { intros b hb. apply hd. intros i _. unfold upd.
      destruct (Nat.eqb_spec i n); [subst; reflexivity | reflexivity]. }
    simpl. rewrite (IH _ (hm1 true) (hdb true) x), (IH _ (hm1 false) (hdb false) x).
    destruct (x n) eqn:hxn.
    + rewrite (hsame true eq_refl).
      assert (hle : LeAssign (upd x n false) x).
      { intro i. unfold upd. destruct (Nat.eqb i n); [reflexivity|].
        destruct (x i); reflexivity. }
      pose proof (hm _ _ hle) as H.
      unfold leB in H.
      destruct (f x), (f (upd x n false)); simpl in *; congruence.
    + rewrite (hsame false eq_refl). simpl. reflexivity.
Qed.

(** * Double rail: general size = monotone size of a partial function *)

(** Double-rail input: variable 2i carries x_i, variable 2i+1 carries ~x_i. *)
Definition dual (x : nat -> bool) : nat -> bool :=
  fun j => if Nat.even j then x (Nat.div2 j) else negb (x (Nat.div2 j)).

Lemma even_double : forall i, Nat.even (2 * i) = true /\ Nat.even (2 * i + 1) = false.
Proof.
  induction i as [|i IH]; [split; reflexivity|].
  replace (2 * S i) with (S (S (2 * i))) by lia.
  replace (S (S (2 * i)) + 1) with (S (S (2 * i + 1))) by lia.
  simpl. exact IH.
Qed.

Theorem dual_even : forall x i, dual x (2 * i) = x i.
Proof.
  intros x i. unfold dual. rewrite (proj1 (even_double i)), Nat.div2_double. reflexivity.
Qed.

Theorem dual_odd : forall x i, dual x (2 * i + 1) = negb (x i).
Proof.
  intros x i. unfold dual. rewrite (proj2 (even_double i)).
  rewrite Nat.add_1_r, Nat.div2_succ_double. reflexivity.
Qed.

(** Push negations to the inputs: (formula for c, formula for ~c). *)
Fixpoint doubleRail (c : Circ) : Circ * Circ :=
  match c with
  | Var i => (Var (2 * i), Var (2 * i + 1))
  | Lit b => (Lit b, Lit (negb b))
  | Conj a b => (Conj (fst (doubleRail a)) (fst (doubleRail b)),
                 Disj (snd (doubleRail a)) (snd (doubleRail b)))
  | Disj a b => (Disj (fst (doubleRail a)) (fst (doubleRail b)),
                 Conj (snd (doubleRail a)) (snd (doubleRail b)))
  | Neg a => (snd (doubleRail a), fst (doubleRail a))
  end.

(** Both rails are monotone, no larger than c, and on consistent inputs
    compute c and ~c. *)
Theorem doubleRail_correct : forall c,
  notFree (fst (doubleRail c)) = true /\ notFree (snd (doubleRail c)) = true /\
  size (fst (doubleRail c)) <= size c /\ size (snd (doubleRail c)) <= size c /\
  forall x, eval (fst (doubleRail c)) (dual x) = eval c x /\
            eval (snd (doubleRail c)) (dual x) = negb (eval c x).
Proof.
  induction c as [i|b|a IHa b IHb|a IHa b IHb|a IHa]; simpl.
  - split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    intro x. split; [apply dual_even | apply dual_odd].
  - split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    intro x. split; reflexivity.
  - destruct IHa as [a1 [a2 [a3 [a4 a5]]]]. destruct IHb as [b1 [b2 [b3 [b4 b5]]]].
    split; [rewrite a1, b1; reflexivity|].
    split; [rewrite a2, b2; reflexivity|].
    split; [lia|]. split; [lia|].
    intro x. destruct (a5 x) as [e1 e2]. destruct (b5 x) as [e3 e4].
    rewrite e1, e2, e3, e4. destruct (eval a x), (eval b x); split; reflexivity.
  - destruct IHa as [a1 [a2 [a3 [a4 a5]]]]. destruct IHb as [b1 [b2 [b3 [b4 b5]]]].
    split; [rewrite a1, b1; reflexivity|].
    split; [rewrite a2, b2; reflexivity|].
    split; [lia|]. split; [lia|].
    intro x. destruct (a5 x) as [e1 e2]. destruct (b5 x) as [e3 e4].
    rewrite e1, e2, e3, e4. destruct (eval a x), (eval b x); split; reflexivity.
  - destruct IHa as [a1 [a2 [a3 [a4 a5]]]].
    split; [exact a2|]. split; [exact a1|]. split; [lia|]. split; [lia|].
    intro x. destruct (a5 x) as [e1 e2]. rewrite e1, e2.
    destruct (eval a x); split; reflexivity.
Qed.

(** Replace double-rail inputs by x_i and ~x_i. *)
Fixpoint undual (c : Circ) : Circ :=
  match c with
  | Var j => if Nat.even j then Var (Nat.div2 j) else Neg (Var (Nat.div2 j))
  | Lit b => Lit b
  | Conj a b => Conj (undual a) (undual b)
  | Disj a b => Disj (undual a) (undual b)
  | Neg a => Neg (undual a)
  end.

(** [undual] turns a double-rail formula into a general formula at most
    twice as large. *)
Theorem undual_correct : forall c,
  size (undual c) <= 2 * size c /\ forall x, eval (undual c) x = eval c (dual x).
Proof.
  induction c as [j|b|a IHa b IHb|a IHa b IHb|a IHa]; simpl.
  - unfold dual. destruct (Nat.even j); simpl; split; auto.
  - split; [lia | reflexivity].
  - destruct IHa as [s1 e1], IHb as [s2 e2].
    split; [lia|]. intro x. rewrite e1, e2. reflexivity.
  - destruct IHa as [s1 e1], IHb as [s2 e2].
    split; [lia|]. intro x. rewrite e1, e2. reflexivity.
  - destruct IHa as [s1 e1].
    split; [lia|]. intro x. rewrite e1. reflexivity.
Qed.

(** * Lower-bound statements *)

(** Schema: the family f n has no general formulas of polynomial size.  The
    family is a parameter, so this is a schema; its instance for SAT is
    [SATFormulaLowerBound]. *)
Definition GeneralSuperpolyLowerBoundFor (f : nat -> (nat -> bool) -> bool) : Prop :=
  forall c d : nat, exists n, forall C : Circ,
    size C <= c * n ^ d + c -> exists x, eval C x <> f n x.

(** Schema: a superpolynomial lower bound against monotone formulas only. *)
Definition MonotoneSuperpolyLowerBoundFor (f : nat -> (nat -> bool) -> bool) : Prop :=
  forall c d : nat, exists n, forall C : Circ, notFree C = true ->
    size C <= c * n ^ d + c -> exists x, eval C x <> f n x.

(** Schema: a monotone lower bound for the double-rail partial function
    (correct only on inputs [dual x]). *)
Definition DoubleRailLowerBoundFor (f : nat -> (nat -> bool) -> bool) : Prop :=
  forall c d : nat, exists n, forall C : Circ, notFree C = true ->
    size C <= c * n ^ d + c -> exists x, eval C (dual x) <> f n x.

(** The easy direction: a general lower bound restricts to monotone formulas. *)
Theorem general_lb_implies_monotone_lb : forall f,
  GeneralSuperpolyLowerBoundFor f -> MonotoneSuperpolyLowerBoundFor f.
Proof.
  intros f h c d. destruct (h c d) as [n hn].
  exists n. intros C _ hs. exact (hn C hs).
Qed.

(** Exact reformulation: a general superpolynomial lower bound holds iff a
    monotone superpolynomial lower bound holds for the double-rail partial
    function. *)
Theorem general_iff_double_rail : forall f,
  GeneralSuperpolyLowerBoundFor f <-> DoubleRailLowerBoundFor f.
Proof.
  intro f. split.
  - intros h c d. destruct (h (2 * c) d) as [n hn].
    exists n. intros C _ hs.
    destruct (undual_correct C) as [hsz he].
    assert (hsz' : size (undual C) <= 2 * c * n ^ d + 2 * c) by nia.
    destruct (hn (undual C) hsz') as [x hx].
    exists x. rewrite <- he. exact hx.
  - intros h c d. destruct (h c d) as [n hn].
    exists n. intros C hs.
    destruct (doubleRail_correct C) as [d1 [_ [d3 [_ d5]]]].
    destruct (hn (fst (doubleRail C)) d1 (Nat.le_trans _ _ _ d3 hs)) as [x hx].
    exists x. rewrite <- (proj1 (d5 x)). exact hx.
Qed.

(** * The obligation on the shared machine model *)

(** Open obligation.  SAT (the language [SAT] of Machines.v) has no
    polynomial-size formulas: for every c d there is a length n at which no
    formula of size at most c * n ^ d + c computes SAT on the words of
    length n (read from variables 0, ..., n - 1). *)
Definition SATFormulaLowerBound : Prop :=
  forall c d : nat, exists n, forall C : Circ,
    size C <= c * n ^ d + c -> exists x, eval C x <> slice SAT n x.

Theorem satFormulaLowerBound_iff_for :
  SATFormulaLowerBound <-> GeneralSuperpolyLowerBoundFor (slice SAT).
Proof. reflexivity. Qed.

(** Open obligation (the honest target).  Some language with [InNP] has no
    polynomial-size formulas. *)
Definition NPNotInPolyFormulas : Prop :=
  exists L : Language, InNP L /\
    forall c d : nat, exists n, forall C : Circ,
      size C <= c * n ^ d + c -> exists x, eval C x <> slice L n x.

(** Conditional theorem (honest conclusion).  With [SATInNP], a formula
    lower bound for SAT puts NP outside polynomial-size formulas. *)
Theorem npNotInPolyFormulas_of_sat :
  SATInNP -> SATFormulaLowerBound -> NPNotInPolyFormulas.
Proof. intros mem h. exists SAT. split; [exact mem | exact h]. Qed.

(** Not known, and not assumed anywhere: every language in P has
    polynomial-size formulas.  This is a P in NC1-type statement, an open
    problem that is widely believed false.  It is stated only to show what a
    formula lower bound would additionally need in order to give P <> NP. *)
Definition PSubsetPolyFormulas : Prop :=
  forall L : Language, InP L -> exists c d : nat, forall n, exists C : Circ,
    size C <= c * n ^ d + c /\ forall x, eval C x = slice L n x.

(** The gap, made explicit: a formula lower bound for SAT gives P <> NP only
    together with the unproved [PSubsetPolyFormulas]. *)
Theorem pNotEqualsNP_of_satFormulaLowerBound :
  SATInNP -> PSubsetPolyFormulas -> SATFormulaLowerBound -> PNotEqualsNP.
Proof.
  intros mem hPF h hPNP.
  destruct (hPF SAT (hPNP SAT mem)) as [c [d hc]].
  destruct (h c d) as [n hn].
  destruct (hc n) as [C [hs hC]].
  destruct (hn C hs) as [x hx].
  exact (hx (hC x)).
Qed.

(** The double-rail reformulation applies to SAT. *)
Theorem satFormulaLowerBound_iff_doubleRail :
  SATFormulaLowerBound <-> DoubleRailLowerBoundFor (slice SAT).
Proof. exact (general_iff_double_rail (slice SAT)). Qed.

(** SAT on words is not monotone at length 2: 00 encodes the empty formula
    (satisfiable) and 10 encodes the empty clause (unsatisfiable). *)
Theorem sat_slice_not_monotone : ~ MonotoneFn (slice SAT 2).
Proof.
  intro h.
  assert (hle : LeAssign (fun _ => false) (fun i => Nat.eqb i 0)).
  { intro i. reflexivity. }
  specialize (h _ _ hle).
  assert (h1 : slice SAT 2 (fun _ => false) = true) by (vm_compute; reflexivity).
  assert (h2 : slice SAT 2 (fun i => Nat.eqb i 0) = false) by (vm_compute; reflexivity).
  rewrite h1, h2 in h. discriminate h.
Qed.

(** The monotone lower bound for SAT holds for a trivial reason (no
    monotone formula computes SAT at length 2), so it says nothing about the
    size of formulas for SAT.  The Rocq proof is constructive: it tests the
    two assignments used in [sat_slice_not_monotone]. *)
Theorem sat_monotone_lower_bound_trivial : MonotoneSuperpolyLowerBoundFor (slice SAT).
Proof.
  intros c d. exists 2. intros C hC _.
  assert (hle : LeAssign (fun _ => false) (fun i => Nat.eqb i 0)).
  { intro i. reflexivity. }
  assert (h1 : slice SAT 2 (fun _ => false) = true) by (vm_compute; reflexivity).
  assert (h2 : slice SAT 2 (fun i => Nat.eqb i 0) = false) by (vm_compute; reflexivity).
  destruct (eval C (fun _ => false)) eqn:e0.
  - exists (fun i => Nat.eqb i 0).
    pose proof (monotone_eval C hC _ _ hle) as hm.
    rewrite e0 in hm. unfold leB in hm. simpl in hm. rewrite hm, h2. discriminate.
  - exists (fun _ => false). rewrite e0, h1. discriminate.
Qed.

(** Non-vacuity (false side): the lower-bound shape fails for a constant
    family, which the one-node formula [Lit b] computes at every length. *)
Theorem const_no_general_lower_bound : forall b : bool,
  ~ GeneralSuperpolyLowerBoundFor (fun _ _ => b).
Proof.
  intros b h. destruct (h 1 0) as [n hn].
  destruct (hn (Lit b)) as [x hx].
  - simpl. lia.
  - exact (hx eq_refl).
Qed.
