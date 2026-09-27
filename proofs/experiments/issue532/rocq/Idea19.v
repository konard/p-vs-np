(* Issue #532, Idea 19: advice and nonuniformity.

   Rocq counterpart of lean/Idea19.lean.  Every unary language (computable or
   not) is decided by one fixed machine with one bit of advice per length
   (unary_decided_by_advice); the one-bit-advice class escapes every
   nat-indexed family of languages (advice_escapes_every_enumeration), so it
   contains undecidable languages; input-dependent advice decides everything
   (input_advice_trivializes); a fixed machine with at most n advice bits
   cannot decide every language on length-n inputs
   (fixed_machine_advice_limited).  Verdict: advice is refuted as a route to
   uniform P = NP; the converse direction reduces to the open obligation
   NPNotInPPoly (only defined), via nonuniform_lower_bound_separates. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

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

(* ---------- The only useful direction ---------- *)

Definition Lang := list bool -> bool.

Theorem uniform_in_advice : forall D : Lang,
  AdviceDecides (fun x (_ : list bool) => D x) (fun _ => []) D.
Proof. intros D x. reflexivity. Qed.

(* Open obligation: some language of NP lies outside the nonuniform class
   PPoly.  Only defined. *)
Definition NPNotInPPoly (NP PPoly : Lang -> Prop) : Prop :=
  exists L, NP L /\ ~ PPoly L.

Theorem not_in_superclass_not_in_P : forall (P C : Lang -> Prop),
  (forall L, P L -> C L) -> forall L, ~ C L -> ~ P L.
Proof. intros P C HPC L HL HP. apply HL. apply HPC. exact HP. Qed.

Theorem nonuniform_lower_bound_separates : forall (P NP PPoly : Lang -> Prop),
  (forall L, P L -> PPoly L) -> NPNotInPPoly NP PPoly -> ~ (forall L, NP L -> P L).
Proof.
  intros P NP PPoly HP [L [HL Hnot]] HNP.
  apply (not_in_superclass_not_in_P P PPoly HP L Hnot). apply HNP. exact HL.
Qed.
