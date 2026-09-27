(* Issue #532, Idea 34: quantifier order in lower bounds.

   Rocq counterpart of ../lean/Idea34.lean, importing the repository's
   machine model (proofs/complexity/rocq/Complexity.v).

   Proved: the valid quantifier direction (exists-forall to forall-exists),
   the failure of its converse on every type with two distinct elements,
   PNotEqualsNP <-> exists L, InNP L /\ ~ InP L, the constructive unfolding
   ~ InP L <-> forall p : ClassP, p_language p <> L, the per-algorithm form
   (forall p, exists x, p errs on x), and, in the function model, that no
   finite set of inputs is hard for every algorithm of a class closed under
   finite patching, while hard inputs of such a class occur at arbitrarily
   large sizes.

   Logical dependencies: pNotEqualsNP_imp_exists_hard, language_ne_iff,
   not_inP_iff_each_errs, pNotEqualsNP_iff_unfolded and hard_inputs_unbounded
   use classical logic (Classical_Prop) and, for language_ne_iff,
   functional extensionality. All other theorems use no extra logical principles. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
From Stdlib Require Import Classical_Prop FunctionalExtensionality.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.
Import ListNotations.

(* (a) Pure quantifier logic. *)

Theorem exists_forall_imp_forall_exists {A B : Type} (R : A -> B -> Prop) :
  (exists x, forall a, R a x) -> forall a, exists x, R a x.
Proof. intros [x Hx] a. exists x. apply Hx. Qed.

Theorem forall_exists_not_imp_exists_forall {A : Type} (a0 a1 : A) :
  a0 <> a1 ->
  exists R : A -> A -> Prop, (forall a, exists x, R a x) /\ ~ exists x, forall a, R a x.
Proof.
  intro Hne. exists (fun a x => a = x). split.
  - intro a. exists a. reflexivity.
  - intros [x Hx]. apply Hne. rewrite (Hx a0), (Hx a1). reflexivity.
Qed.

Example bool_instance :
  exists R : bool -> bool -> Prop, (forall a, exists x, R a x) /\ ~ exists x, forall a, R a x.
Proof. apply (forall_exists_not_imp_exists_forall false true). discriminate. Qed.

(* (b), (c) Quantifier structure of PNotEqualsNP. *)

Theorem exists_hard_imp_pNotEqualsNP :
  (exists L, InNP L /\ ~ InP L) -> PNotEqualsNP.
Proof. intros [L [HNP HP]] HEq. exact (HP (HEq L HNP)). Qed.

Theorem pNotEqualsNP_imp_exists_hard :
  PNotEqualsNP -> exists L, InNP L /\ ~ InP L.
Proof.
  intro Hne. apply NNPP. intro Hno. apply Hne. intros L HNP.
  apply NNPP. intro HP. apply Hno. exists L. split; assumption.
Qed.

Theorem pNotEqualsNP_iff_exists_hard :
  PNotEqualsNP <-> exists L, InNP L /\ ~ InP L.
Proof.
  split; [apply pNotEqualsNP_imp_exists_hard | apply exists_hard_imp_pNotEqualsNP].
Qed.

Theorem not_inP_iff (L : Language) :
  ~ InP L <-> forall p : ClassP, p_language p <> L.
Proof.
  split.
  - intros H p Hp. apply H. exists p. exact Hp.
  - intros H [p Hp]. exact (H p Hp).
Qed.

Theorem language_ne_iff (L1 L2 : Language) :
  L1 <> L2 <-> exists x, L1 x <> L2 x.
Proof.
  split.
  - intro Hne. apply NNPP. intro Hno. apply Hne.
    apply functional_extensionality. intro x.
    apply NNPP. intro Hx. apply Hno. exists x. exact Hx.
  - intros [x Hx] Heq. apply Hx. rewrite Heq. reflexivity.
Qed.

Theorem not_inP_iff_each_errs (L : Language) :
  ~ InP L <-> forall p : ClassP, exists x, p_language p x <> L x.
Proof.
  rewrite not_inP_iff. split.
  - intros H p. apply language_ne_iff. apply H.
  - intros H p. apply language_ne_iff. apply H.
Qed.

Theorem pNotEqualsNP_iff_unfolded :
  PNotEqualsNP <->
  exists L, InNP L /\ forall p : ClassP, exists x, p_language p x <> L x.
Proof.
  rewrite pNotEqualsNP_iff_exists_hard. split.
  - intros [L [H1 H2]]. exists L. split; [exact H1|apply not_inP_iff_each_errs; exact H2].
  - intros [L [H1 H2]]. exists L. split; [exact H1|apply not_inP_iff_each_errs; exact H2].
Qed.

(* Finite patching in the function model. *)

Fixpoint word_eqb (x y : Word) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => Bool.eqb a b && word_eqb x' y'
  | _, _ => false
  end.

Lemma word_eqb_refl : forall x, word_eqb x x = true.
Proof. induction x as [|a x IH]; simpl; [reflexivity|]. rewrite Bool.eqb_reflx. exact IH. Qed.

Fixpoint memb (x : Word) (xs : list Word) : bool :=
  match xs with
  | [] => false
  | y :: ys => word_eqb x y || memb x ys
  end.

Lemma memb_of_mem : forall x xs, In x xs -> memb x xs = true.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl; intro H; [destruct H|].
  destruct H as [H|H].
  - subst. rewrite word_eqb_refl. reflexivity.
  - rewrite IH by exact H. apply orb_true_r.
Qed.

Definition patch (A L : Word -> bool) (xs : list Word) (x : Word) : bool :=
  if memb x xs then L x else A x.

Theorem lookup_agrees (A L : Word -> bool) (xs : list Word) :
  forall x, In x xs -> patch A L xs x = L x.
Proof. intros x Hx. unfold patch. rewrite (memb_of_mem x xs Hx). reflexivity. Qed.

Theorem patch_outside (A L : Word -> bool) (xs : list Word) (x : Word) :
  memb x xs = false -> patch A L xs x = A x.
Proof. intro H. unfold patch. rewrite H. reflexivity. Qed.

Definition PatchClosed (Alg : (Word -> bool) -> Prop) (L : Word -> bool) : Prop :=
  forall A xs, Alg A -> Alg (patch A L xs).

Theorem no_universal_hard_input (Alg : (Word -> bool) -> Prop) (L : Word -> bool) :
  PatchClosed Alg L -> forall A, Alg A ->
  ~ exists x, forall B, Alg B -> B x <> L x.
Proof.
  intros Hclosed A HA [x Hx].
  apply (Hx (patch A L [x]) (Hclosed A [x] HA)).
  apply lookup_agrees. left. reflexivity.
Qed.

Theorem no_universal_hard_input_set (Alg : (Word -> bool) -> Prop) (L : Word -> bool) :
  PatchClosed Alg L -> forall A, Alg A ->
  ~ exists xs : list Word, forall B, Alg B -> exists x, In x xs /\ B x <> L x.
Proof.
  intros Hclosed A HA [xs Hxs].
  destruct (Hxs (patch A L xs) (Hclosed A xs HA)) as [x [Hmem Hne]].
  apply Hne. apply lookup_agrees. exact Hmem.
Qed.

Fixpoint allInputs (n : nat) : list Word :=
  match n with
  | 0 => [[]]
  | S n => map (cons false) (allInputs n) ++ map (cons true) (allInputs n)
  end.

Lemma mem_allInputs : forall x : Word, In x (allInputs (length x)).
Proof.
  induction x as [|b x IH]; simpl; [left; reflexivity|].
  apply in_or_app. destruct b; [right|left]; apply in_map; exact IH.
Qed.

Fixpoint inputsBelow (m : nat) : list Word :=
  match m with
  | 0 => []
  | S m => inputsBelow m ++ allInputs m
  end.

Lemma mem_inputsBelow : forall x m, length x < m -> In x (inputsBelow m).
Proof.
  intros x m. induction m as [|m IH]; intro H; [lia|].
  simpl. apply in_or_app.
  destruct (Nat.eq_dec (length x) m) as [Heq|Hneq].
  - right. rewrite <- Heq. apply mem_allInputs.
  - left. apply IH. lia.
Qed.

Theorem hard_inputs_unbounded (Alg : (Word -> bool) -> Prop) (L : Word -> bool) :
  PatchClosed Alg L ->
  (forall B, Alg B -> exists x, B x <> L x) ->
  forall A, Alg A -> forall m, exists x, m <= length x /\ A x <> L x.
Proof.
  intros Hclosed HnoSolver A HA m.
  destruct (HnoSolver (patch A L (inputsBelow m)) (Hclosed A _ HA)) as [x Hx].
  exists x. split.
  - apply NNPP. intro Hlt. apply Hx. apply lookup_agrees.
    apply mem_inputsBelow. lia.
  - intro HAx. apply Hx. unfold patch.
    destruct (memb x (inputsBelow m)); [reflexivity|exact HAx].
Qed.
