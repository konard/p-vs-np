(* Issue #532, Idea 19: advice and nonuniformity.

   Rocq counterpart of lean/Idea19.lean; theorem names are aligned.  Every
   unary language (computable or not) is decided by one fixed machine with
   one bit of advice per length (unary_decided_by_advice); the
   one-bit-advice class escapes every nat-indexed family of languages
   (advice_escapes_every_enumeration), so it contains undecidable languages;
   input-dependent advice decides everything (input_advice_trivializes); a
   fixed machine with at most n advice bits cannot decide every language on
   length-n inputs (fixed_machine_advice_limited).

   In the shared model: every length-only language is in InPPoly
   (inPPoly_lengthOnly), and a unary diagonal against (machine, polynomial)
   pairs is not in InP (unaryDiag_not_inP), so P/poly is not contained in P
   (ppoly_not_subset_p).

   Verdict: advice is refuted as a route to a uniform polynomial algorithm.
   The converse direction is developed to the open obligations SATNotInPPoly
   (~ InPPoly SAT) and NPNotInPPoly (NP not in P/poly), stated over the
   shared machine and circuit models.  With SATInNP and the known theorem
   PSubsetPPoly as named hypotheses they give PNotEqualsNP
   (pNotEqualsNP_of_satNotInPPoly, pNotEqualsNP_of_npNotInPPoly).  Neither
   obligation is proved.

   Differences from Lean: the escape statements are pointwise (no function
   extensionality); unaryDiag is computable (it diagonalises with the
   step-bounded interpreter runFor against the pairs decoded by
   decMachinePoly) where the Lean one is noncomputable; and
   satNotInPPoly_iff_superpoly takes excluded middle as an explicit premise,
   like superpoly_iff_not_inPPoly in Circuits.v. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.

(* ---------- Advice machines ---------- *)

Definition AdviceDecides {A : Type} (M : list A -> list bool -> bool)
  (a : nat -> list bool) (L : list A -> bool) : Prop :=
  forall x, M x (a (length x)) = L x.

Definition readAdvice {A : Type} (_x : list A) (adv : list bool) : bool :=
  match adv with
  | [] => false
  | b :: _ => b
  end.

Definition unaryLang (U : nat -> bool) (x : list unit) : bool := U (length x).

Definition adviceOf (U : nat -> bool) (n : nat) : list bool := [U n].

Theorem adviceOf_length : forall U n, length (adviceOf U n) = 1.
Proof. reflexivity. Qed.

Theorem unary_decided_by_advice : forall U : nat -> bool,
  AdviceDecides readAdvice (adviceOf U) (unaryLang U).
Proof. intros U x. reflexivity. Qed.

Theorem adviceOf_injective : forall U V : nat -> bool,
  (forall n, adviceOf U n = adviceOf V n) -> forall n, U n = V n.
Proof.
  intros U V H n. specialize (H n). unfold adviceOf in H. injection H as H. exact H.
Qed.

Theorem advice_escapes_every_enumeration : forall e : nat -> nat -> bool,
  exists U : nat -> bool, (forall i, exists n, U n <> e i n) /\
    AdviceDecides readAdvice (adviceOf U) (unaryLang U).
Proof.
  intros e. exists (fun n => negb (e n n)). split.
  - intros i. exists i. destruct (e i i); discriminate.
  - apply unary_decided_by_advice.
Qed.

Theorem no_enumeration_of_advice_class :
  ~ exists e : nat -> nat -> bool, forall U : nat -> bool,
      AdviceDecides readAdvice (adviceOf U) (unaryLang U) ->
      exists i, forall n, e i n = U n.
Proof.
  intros [e He].
  destruct (advice_escapes_every_enumeration e) as [U [HU Hdec]].
  destruct (He U Hdec) as [i Hi].
  destruct (HU i) as [n Hn]. apply Hn. symmetry. apply Hi.
Qed.

Theorem input_advice_trivializes : forall (A : Type) (L : A -> bool) (x : A),
  (fun (_ : A) (b : bool) => b) x (L x) = L x.
Proof. reflexivity. Qed.

(* ---------- Limits of a fixed machine with short advice ---------- *)

Fixpoint allVecs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allVecs n') ++ map (cons true) (allVecs n')
  end.

Theorem allVecs_length : forall n, length (allVecs n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allVecs : forall n v, In v (allVecs n) <-> length v = n.
Proof.
  induction n as [|n IH]; intros v; simpl.
  - split.
    + intros [H|[]]. subst. reflexivity.
    + intros H. destruct v; [left; reflexivity | discriminate].
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; subst; simpl; f_equal; apply IH; exact Hin.
    + intros H. destruct v as [|b w]; [discriminate|].
      simpl in H. injection H as H.
      destruct b; [right|left]; exists w; split; auto; apply IH; exact H.
Qed.

Fixpoint toNat (x : list bool) : nat :=
  match x with
  | [] => 0
  | b :: x' => (if b then 1 else 0) + 2 * toNat x'
  end.

Fixpoint fromNat (n i : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => Nat.eqb (i mod 2) 1 :: fromNat n' (i / 2)
  end.

Theorem fromNat_length : forall n i, length (fromNat n i) = n.
Proof. induction n as [|n IH]; intros i; simpl; auto. Qed.

Theorem toNat_fromNat : forall n i, i < 2 ^ n -> toNat (fromNat n i) = i.
Proof.
  induction n as [|n IH]; intros i Hi.
  - simpl in Hi. simpl. lia.
  - rewrite Nat.pow_succ_r' in Hi.
    pose proof (Nat.div_mod_eq i 2) as Hdm.
    pose proof (Nat.mod_upper_bound i 2 ltac:(lia)) as Hm.
    assert (Hdiv : i / 2 < 2 ^ n) by lia.
    cbn [fromNat toNat]. rewrite (IH (i / 2) Hdiv).
    destruct (Nat.eqb (i mod 2) 1) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + apply Nat.eqb_neq in E. lia.
Qed.

Fixpoint nth (A : list (list bool)) (i : nat) : list bool :=
  match A, i with
  | [], _ => []
  | w :: _, 0 => w
  | _ :: A', S i' => nth A' i'
  end.

Theorem nth_of_mem : forall A w, In w A -> exists i, i < length A /\ nth A i = w.
Proof.
  induction A as [|u A IH]; intros w H; [destruct H|].
  destruct H as [H|H].
  - exists 0. simpl. split; [lia | auto].
  - destruct (IH w H) as [i [Hi Hn]]. exists (S i). simpl. split; [lia | auto].
Qed.

Theorem diagonal_against_advice_list :
  forall (M : list bool -> list bool -> bool) n (A : list (list bool)),
    length A <= 2 ^ n ->
    exists L : list bool -> bool, forall w, In w A ->
      exists x, length x = n /\ M x w <> L x.
Proof.
  intros M n A HA. exists (fun x => negb (M x (nth A (toNat x)))).
  intros w Hw. destruct (nth_of_mem A w Hw) as [i [Hi Hn]].
  exists (fromNat n i). split; [apply fromNat_length|].
  rewrite toNat_fromNat by lia. rewrite Hn.
  destruct (M (fromNat n i) w); discriminate.
Qed.

Theorem fixed_machine_advice_limited :
  forall (M : list bool -> list bool -> bool) n s, s <= n ->
    exists L : list bool -> bool, forall w, length w = s ->
      exists x, length x = n /\ M x w <> L x.
Proof.
  intros M n s Hs.
  assert (Hlen : length (allVecs s) <= 2 ^ n).
  { rewrite allVecs_length. apply Nat.pow_le_mono_r; lia. }
  destruct (diagonal_against_advice_list M n (allVecs s) Hlen) as [L HL].
  exists L. intros w Hw. apply HL. apply mem_allVecs. exact Hw.
Qed.

(* ---------- Advice in the shared model: P/poly contains undecidable languages ---------- *)

(** Every language that depends only on the input length is in P/poly: at
    length n the circuit is the constant [U n]. *)
Theorem inPPoly_lengthOnly : forall U : nat -> bool, InPPoly (fun x => U (length x)).
Proof.
  intro U. exists {| coefficient := 3; degree := 0 |}. intros n hn.
  destruct (U n) eqn:hU.
  - exists [(0, 0); (0, n)].
    split; [unfold evalPoly; simpl; lia |].
    split; [unfold WF; simpl; repeat split; lia |].
    intros x hx. subst n. rewrite hU. apply output_const_true. exact hn.
  - exists [(0, 0); (0, n); (n + 1, n + 1)].
    split; [unfold evalPoly; simpl; lia |].
    split; [unfold WF; simpl; repeat split; lia |].
    intros x hx. subst n. rewrite hU. apply output_const_false. exact hn.
Qed.

(** Bijective base-2 numeral of a word; injective. *)
Fixpoint bijNat (w : Word) : nat :=
  match w with
  | [] => 0
  | b :: w' => 2 * bijNat w' + (if b then 2 else 1)
  end.

(** Inverse of [bijNat], by recursion on a fuel bound (Rocq only; Lean
    proves injectivity directly). *)
Fixpoint bijWord (fuel n : nat) : Word :=
  match fuel, n with
  | 0, _ => []
  | _, 0 => []
  | S f, S n' => Nat.odd n' :: bijWord f (Nat.div2 n')
  end.

Lemma bijWord_bijNat : forall w fuel, length w <= fuel -> bijWord fuel (bijNat w) = w.
Proof.
  induction w as [|b w IH]; intros fuel h.
  - destruct fuel; reflexivity.
  - destruct fuel as [|f]; simpl in h; [lia|].
    assert (e : bijNat (b :: w) = S (2 * bijNat w + (if b then 1 else 0))).
    { simpl. destruct b; lia. }
    rewrite e. cbn [bijWord]. f_equal.
    + destruct b; rewrite Nat.add_comm.
      * rewrite Nat.add_1_l. rewrite Nat.odd_succ, Nat.even_mul. reflexivity.
      * rewrite Nat.add_0_l, Nat.odd_mul. reflexivity.
    + rewrite <- (IH f) at 2 by lia. f_equal.
      destruct b; rewrite Nat.add_comm.
      * rewrite Nat.add_1_l. apply Nat.div2_succ_double.
      * rewrite Nat.add_0_l. apply Nat.div2_double.
Qed.

Lemma length_le_bijNat : forall w, length w <= bijNat w.
Proof. induction w as [|b w IH]; simpl; [lia|]. destruct b; lia. Qed.

Theorem bijNat_injective : forall v w : Word, bijNat v = bijNat w -> v = w.
Proof.
  intros v w h.
  rewrite <- (bijWord_bijNat v (bijNat v)) by apply length_le_bijNat.
  rewrite <- (bijWord_bijNat w (bijNat w)) by apply length_le_bijNat.
  rewrite h. reflexivity.
Qed.

(** The unary diagonal: length n is accepted unless n numbers (via
    [bijNat]) the code of a pair (m, p) such that m accepts the all-true word
    of length n within p(n) steps.  Unlike the Lean [unaryDiag]
    (noncomputable, unbounded runs of all machines), this one is computable:
    it uses the decoder [decMachinePoly] and [clockedLanguage] (the
    step-bounded interpreter [runFor]) of Machines.v. *)
Definition unaryDiag (n : nat) : bool :=
  match decMachinePoly (bijWord n n) with
  | Some x => negb (clockedLanguage x (repeat true n))
  | None => true
  end.

(** No machine decides the unary diagonal in polynomial time. *)
Theorem unaryDiag_not_inP : ~ InP (fun x => unaryDiag (length x)).
Proof.
  intro h. apply polyDec_iff_inP in h. destruct h as [m [p hd]].
  set (w := encMachinePoly (m, p)).
  set (n := bijNat w).
  destruct (hd (repeat true n)) as [t [b [ht [hr hb]]]].
  rewrite repeat_length in ht, hb.
  assert (hw : bijWord n n = w) by (apply bijWord_bijNat; apply length_le_bijNat).
  assert (hD : unaryDiag n = negb b).
  { unfold unaryDiag. rewrite hw. unfold w. rewrite decMachinePoly_encMachinePoly.
    unfold clockedLanguage. simpl fst. simpl snd. rewrite repeat_length.
    rewrite (runFor_of_run _ _ _ _ hr _ ht). destruct b; reflexivity. }
  rewrite hD in hb. destruct b; discriminate hb.
Qed.

(** P/poly is not contained in P (in the shared model): the unary diagonal
    is in P/poly and not in P.  Advice buys non-uniformity, not algorithms. *)
Theorem ppoly_not_subset_p : exists L : Language, InPPoly L /\ ~ InP L.
Proof.
  exists (fun x => unaryDiag (length x)).
  split; [apply inPPoly_lengthOnly | apply unaryDiag_not_inP].
Qed.

(* ---------- The only useful direction: lower bounds against nonuniform classes ---------- *)

Definition Lang := list bool -> bool.

(** A uniform decider is an advice machine that ignores empty advice: the
    abstract content of P in P/poly. *)
Theorem uniform_in_advice : forall D : Lang,
  AdviceDecides (fun x (_ : list bool) => D x) (fun _ => []) D.
Proof. intros D x. reflexivity. Qed.

(** Schema (the pre-refactor form): some language of a class NP lies outside
    a class PPoly.  Both classes are parameters, so the schema is only as
    strong as the classes supplied; [NPNotInPPoly] is its instance at the
    shared [InNP] and [InPPoly]. *)
Definition NPNotInPPolyFor (NP PPoly : Lang -> Prop) : Prop :=
  exists L, NP L /\ ~ PPoly L.

Theorem not_in_superclass_not_in_P : forall (P C : Lang -> Prop),
  (forall L, P L -> C L) -> forall L, ~ C L -> ~ P L.
Proof. intros P C HPC L HL HP. apply HL. apply HPC. exact HP. Qed.

(** Schema version of the conditional separation: if P is contained in PPoly
    and the schema holds, then NP is not contained in P. *)
Theorem nonuniform_lower_bound_separatesFor : forall (P NP PPoly : Lang -> Prop),
  (forall L, P L -> PPoly L) -> NPNotInPPolyFor NP PPoly -> ~ (forall L, NP L -> P L).
Proof.
  intros P NP PPoly HP [L [HL Hnot]] HNP.
  apply (not_in_superclass_not_in_P P PPoly HP L Hnot). apply HNP. exact HL.
Qed.

(* ---------- The open obligations over the shared model ---------- *)

(** Open obligation.  SAT ([SAT] of Machines.v) is not in P/poly ([InPPoly]
    of Circuits.v).  Classically equivalent to [SuperpolyLowerBound SAT]. *)
Definition SATNotInPPoly : Prop := ~ InPPoly SAT.

(** Open obligation.  NP is not contained in P/poly: some language in the
    shared [InNP] is outside the shared [InPPoly]. *)
Definition NPNotInPPoly : Prop := exists L : Language, InNP L /\ ~ InPPoly L.

Theorem npNotInPPoly_iff_for : NPNotInPPoly <-> NPNotInPPolyFor InNP InPPoly.
Proof. reflexivity. Qed.

(** Lean derives this from [superpoly_iff_not_inPPoly], which is classical;
    here excluded middle is an explicit premise [classic] (not an axiom).
    The direction [SuperpolyLowerBound SAT -> SATNotInPPoly] is
    [not_inPPoly_of_superpoly] and needs no premise. *)
Theorem satNotInPPoly_iff_superpoly : (forall P : Prop, P \/ ~ P) ->
  (SATNotInPPoly <-> SuperpolyLowerBound SAT).
Proof.
  intro classic. unfold SATNotInPPoly. symmetry.
  exact (superpoly_iff_not_inPPoly classic SAT).
Qed.

(** The SAT obligation gives the NP obligation, using [SATInNP]. *)
Theorem npNotInPPoly_of_sat : SATInNP -> SATNotInPPoly -> NPNotInPPoly.
Proof. intros mem h. exists SAT. split; [exact mem | exact h]. Qed.

(** Conditional theorem.  With the known theorem P in P/poly as the named
    hypothesis [PSubsetPPoly], NP not in P/poly gives P <> NP. *)
Theorem pNotEqualsNP_of_npNotInPPoly : PSubsetPPoly -> NPNotInPPoly -> PNotEqualsNP.
Proof.
  intros hP [L [hL hnot]] hEq.
  exact (not_inP_of_not_inPPoly hP L hnot (hEq L hL)).
Qed.

(** Conditional theorem (SAT form).  With [SATInNP] and [PSubsetPPoly] as
    named hypotheses, [~ InPPoly SAT] gives P <> NP.  (Lean goes through
    [SuperpolyLowerBound SAT]; the Rocq proof uses [not_inP_of_not_inPPoly]
    directly and so needs no excluded middle.) *)
Theorem pNotEqualsNP_of_satNotInPPoly :
  SATInNP -> PSubsetPPoly -> SATNotInPPoly -> PNotEqualsNP.
Proof.
  intros mem hP h hEq.
  exact (not_inP_of_not_inPPoly hP SAT h (inP_sat_of_pEqualsNP mem hEq)).
Qed.

(** The schema theorem, instantiated at the shared classes. *)
Theorem nonuniform_lower_bound_separates : PSubsetPPoly -> NPNotInPPoly ->
  ~ (forall L, InNP L -> InP L).
Proof. exact (nonuniform_lower_bound_separatesFor InP InNP InPPoly). Qed.

(* ---------- Non-vacuity ---------- *)

(** The [~ InPPoly] half is satisfiable (by a counting language not known to
    be in NP), and it is not trivial: constant languages are in P/poly. *)
Theorem not_inPPoly_nonvacuous : (exists L, ~ InPPoly L) /\ InPPoly (fun _ => true).
Proof. split; [exact exists_not_inPPoly | exact (inPPoly_const true)]. Qed.

(** [PSubsetPPoly] is not refuted by [ppoly_not_subset_p]: the converse
    inclusion fails, which is consistent with P in P/poly.  The obligation
    needs a language that is both in NP and outside P/poly. *)
Theorem ppoly_strictly_bigger_than_p_if : PSubsetPPoly ->
  (forall L, InP L -> InPPoly L) /\ exists L, InPPoly L /\ ~ InP L.
Proof. intro hP. split; [exact hP | exact ppoly_not_subset_p]. Qed.
