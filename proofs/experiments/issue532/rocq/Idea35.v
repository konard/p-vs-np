(* Issue #532, Idea 35: exact compression of solution sets.

   Rocq counterpart of ../lean/Idea35.lean (same theorem names and content).
   Boolean functions on n variables are represented by truth tables of length
   2^n; there are 2^(2^n) of them but only 2^(2^n) - 1 bit strings shorter
   than 2^n. Hence every exact representation scheme gives some function a
   representation of length at least 2^n
   (exact_representation_needs_long_codes), and at most 2^b - 1 tables get
   codes shorter than b (few_compressible). The open obligation
   CompactTractableCompilation is equivalent to having a decider.
   All proofs are constructive. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Theorem lossless_injective {X Code : Type} (encode : X -> Code) (decode : Code -> X) :
  (forall x, decode (encode x) = x) -> forall x y, encode x = encode y -> x = y.
Proof.
  intros Hround x y Heq. rewrite <- (Hround x), <- (Hround y), Heq. reflexivity.
Qed.

(* List pigeonhole. *)

Lemma nodup_map_of_inj {A B : Type} (f : A -> B) :
  forall l, NoDup l -> (forall x, In x l -> forall y, In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd Hinj; [constructor|].
  inversion Hnd as [|a' l' Hnot Hl]; subst.
  constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hy]].
    assert (a = y) as Hay by (apply Hinj; auto).
    subst. exact (Hnot Hy).
  - apply IH; [exact Hl|]. intros x Hx y Hy H. apply Hinj; auto.
Qed.

Theorem inj_length_le {A B : Type} (f : A -> B) (l : list A) (l' : list B) :
  NoDup l -> (forall x, In x l -> forall y, In y l -> f x = f y -> x = y) ->
  (forall x, In x l -> In (f x) l') -> length l <= length l'.
Proof.
  intros Hnd Hinj Hmem.
  rewrite <- (length_map f l).
  apply NoDup_incl_length.
  - apply nodup_map_of_inj; assumption.
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [x [Hx Hin]]. subst. auto.
Qed.

(* Enumerations. *)

Fixpoint allInputs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n => map (cons false) (allInputs n) ++ map (cons true) (allInputs n)
  end.

Theorem allInputs_length : forall n, length (allInputs n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem length_of_mem_allInputs :
  forall n x, In x (allInputs n) -> length x = n.
Proof.
  induction n as [|n IH]; simpl; intros x H.
  - destruct H as [H|[]]. subst. reflexivity.
  - apply in_app_or in H. destruct H as [H|H];
      apply in_map_iff in H; destruct H as [y [Hy Hin]]; subst; simpl;
      rewrite (IH y Hin); reflexivity.
Qed.

Theorem mem_allInputs : forall x, In x (allInputs (length x)).
Proof.
  induction x as [|b x IH]; simpl; [left; reflexivity|].
  apply in_or_app. destruct b; [right|left]; apply in_map; exact IH.
Qed.

Lemma nodup_app_disjoint {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l IH]; simpl; intros H1 H2 Hdis; [exact H2|].
  inversion H1 as [|a' l' Hnot Hl]; subst.
  constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (Hnot Hin).
    + exact (Hdis a (or_introl eq_refl) Hin).
  - apply IH; [exact Hl | exact H2 | intros b Hb; apply Hdis; right; exact Hb].
Qed.

Theorem allInputs_nodup : forall n, NoDup (allInputs n).
Proof.
  induction n as [|n IH]; simpl.
  - apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
  - apply nodup_app_disjoint.
    + apply nodup_map_of_inj; [exact IH|]. intros x _ y _ H. inversion H. reflexivity.
    + apply nodup_map_of_inj; [exact IH|]. intros x _ y _ H. inversion H. reflexivity.
    + intros a Ha Hb. apply in_map_iff in Ha. apply in_map_iff in Hb.
      destruct Ha as [y [Hy _]]. destruct Hb as [z [Hz _]]. subst. discriminate.
Qed.

Fixpoint inputsBelow (m : nat) : list (list bool) :=
  match m with
  | 0 => []
  | S m => inputsBelow m ++ allInputs m
  end.

Theorem mem_inputsBelow : forall x m, length x < m -> In x (inputsBelow m).
Proof.
  intros x m. induction m as [|m IH]; intro H; [lia|].
  simpl. apply in_or_app.
  destruct (Nat.eq_dec (length x) m) as [Heq|Hneq].
  - right. rewrite <- Heq. apply mem_allInputs.
  - left. apply IH. lia.
Qed.

Lemma one_le_two_pow : forall m, 1 <= 2 ^ m.
Proof. induction m; simpl; lia. Qed.

Theorem inputsBelow_length : forall m, length (inputsBelow m) = 2 ^ m - 1.
Proof.
  induction m as [|m IH]; simpl; [reflexivity|].
  rewrite length_app, IH, allInputs_length.
  pose proof (one_le_two_pow m). lia.
Qed.

(* Counting theorems for codes. *)

Theorem few_compressible (M b : nat) (code : list bool -> list bool) :
  (forall s, In s (allInputs M) -> forall t, In t (allInputs M) -> code s = code t -> s = t) ->
  length (filter (fun t => length (code t) <? b) (allInputs M)) <= 2 ^ b - 1.
Proof.
  intro Hinj. rewrite <- inputsBelow_length.
  apply (inj_length_le code).
  - apply NoDup_filter. apply allInputs_nodup.
  - intros s Hs t Ht H. apply filter_In in Hs. apply filter_In in Ht.
    apply Hinj; tauto.
  - intros t Ht. apply filter_In in Ht. destruct Ht as [_ Ht].
    apply mem_inputsBelow. apply Nat.ltb_lt. exact Ht.
Qed.

Theorem no_injective_into_shorter (M : nat) (code : list bool -> list bool) :
  (forall s, In s (allInputs M) -> forall t, In t (allInputs M) -> code s = code t -> s = t) ->
  exists t, In t (allInputs M) /\ M <= length (code t).
Proof.
  intro Hinj.
  destruct (filter (fun t => M <=? length (code t)) (allInputs M)) as [|t rest] eqn:E.
  - exfalso.
    assert (Hshort : forall t, In t (allInputs M) -> In (code t) (inputsBelow M)).
    { intros t Ht. apply mem_inputsBelow.
      destruct (M <=? length (code t)) eqn:Hle.
      - assert (In t (filter (fun t => M <=? length (code t)) (allInputs M))) as Hin
          by (apply filter_In; split; assumption).
        rewrite E in Hin. destruct Hin.
      - apply Nat.leb_gt. exact Hle. }
    pose proof (inj_length_le code (allInputs M) (inputsBelow M)
                  (allInputs_nodup M) Hinj Hshort) as H.
    rewrite allInputs_length, inputsBelow_length in H.
    pose proof (one_le_two_pow M). lia.
  - assert (In t (filter (fun t => M <=? length (code t)) (allInputs M))) as Hin
      by (rewrite E; left; reflexivity).
    apply filter_In in Hin. destruct Hin as [Hin Hle].
    exists t. split; [exact Hin|apply Nat.leb_le; exact Hle].
Qed.

(* From truth tables to Boolean functions. *)

Definition truthTable (n : nat) (f : list bool -> bool) : list bool := map f (allInputs n).

Theorem truthTable_length : forall n f, length (truthTable n f) = 2 ^ n.
Proof. intros. unfold truthTable. rewrite length_map. apply allInputs_length. Qed.

Lemma map_eq_imp_eq_on {A B : Type} (f g : A -> B) :
  forall l, map f l = map g l -> forall x, In x l -> f x = g x.
Proof.
  induction l as [|a l IH]; simpl; intros H x Hx; [destruct Hx|].
  inversion H as [[Ha Hl]]. destruct Hx as [Hx|Hx].
  - subst. exact Ha.
  - apply IH; assumption.
Qed.

Theorem truthTable_eq_iff (n : nat) (f g : list bool -> bool) :
  truthTable n f = truthTable n g <-> forall x, length x = n -> f x = g x.
Proof.
  split.
  - intros H x Hx. apply (map_eq_imp_eq_on f g (allInputs n) H).
    rewrite <- Hx. apply mem_allInputs.
  - intro H. unfold truthTable. apply map_ext_in. intros x Hx.
    apply H. apply (length_of_mem_allInputs n x Hx).
Qed.

Fixpoint ofTable (n : nat) (t : list bool) (x : list bool) : bool :=
  match n, x with
  | 0, _ => hd false t
  | S _, [] => false
  | S n', b :: y =>
      if b then ofTable n' (skipn (2 ^ n') t) y else ofTable n' (firstn (2 ^ n') t) y
  end.

Theorem truthTable_ofTable :
  forall n t, length t = 2 ^ n -> truthTable n (ofTable n t) = t.
Proof.
  induction n as [|n IH]; intros t H.
  - destruct t as [|a [|b t]]; simpl in H; try discriminate. reflexivity.
  - unfold truthTable. simpl allInputs. rewrite map_app, !map_map.
    assert (Ht : length (firstn (2 ^ n) t) = 2 ^ n).
    { rewrite length_firstn, H. simpl. lia. }
    assert (Hd : length (skipn (2 ^ n) t) = 2 ^ n).
    { rewrite length_skipn, H. simpl. lia. }
    replace (map (fun x => ofTable (S n) t (false :: x)) (allInputs n))
      with (truthTable n (ofTable n (firstn (2 ^ n) t))) by reflexivity.
    replace (map (fun x => ofTable (S n) t (true :: x)) (allInputs n))
      with (truthTable n (ofTable n (skipn (2 ^ n) t))) by reflexivity.
    rewrite (IH _ Ht), (IH _ Hd). apply firstn_skipn.
Qed.

Definition ExactOn (n : nat) (rep : (list bool -> bool) -> list bool) : Prop :=
  forall f g, rep f = rep g -> forall x, length x = n -> f x = g x.

Theorem exact_representation_needs_long_codes (n : nat)
    (rep : (list bool -> bool) -> list bool) :
  ExactOn n rep -> exists f : list bool -> bool, 2 ^ n <= length (rep f).
Proof.
  intro Hexact.
  assert (Hinj : forall s, In s (allInputs (2 ^ n)) -> forall t, In t (allInputs (2 ^ n)) ->
            rep (ofTable n s) = rep (ofTable n t) -> s = t).
  { intros s Hs t Ht H.
    pose proof (length_of_mem_allInputs _ _ Hs) as Hs'.
    pose proof (length_of_mem_allInputs _ _ Ht) as Ht'.
    pose proof (proj2 (truthTable_eq_iff n _ _) (Hexact _ _ H)) as Heq.
    rewrite (truthTable_ofTable n s Hs'), (truthTable_ofTable n t Ht') in Heq.
    exact Heq. }
  destruct (no_injective_into_shorter (2 ^ n) (fun t => rep (ofTable n t)) Hinj)
    as [t [_ Hlen]].
  exists (ofTable n t). exact Hlen.
Qed.

(* The open obligation: compact and queryable. *)

Definition CompactTractableCompilation {Formula Rep : Type} (size : Formula -> nat)
    (repSize : Rep -> nat) (sat : Formula -> bool) (q : nat -> nat)
    (compile : Formula -> Rep) (query : Rep -> bool) : Prop :=
  (forall phi, repSize (compile phi) <= q (size phi)) /\
  forall phi, query (compile phi) = sat phi.

Theorem compactness_alone_trivial {Formula : Type} (size : Formula -> nat)
    (sat : Formula -> bool) :
  CompactTractableCompilation size size sat (fun s => s) (fun phi => phi) sat.
Proof. split; intros; reflexivity. Qed.

Theorem decider_gives_compilation {Formula : Type} (size : Formula -> nat)
    (sat : Formula -> bool) :
  CompactTractableCompilation size (fun _ : bool => 1) sat (fun _ => 1) sat (fun b => b).
Proof. split; intros; reflexivity. Qed.

Theorem compilation_decides {Formula Rep : Type} (size : Formula -> nat)
    (repSize : Rep -> nat) (sat : Formula -> bool) (q : nat -> nat)
    (compile : Formula -> Rep) (query : Rep -> bool) :
  CompactTractableCompilation size repSize sat q compile query ->
  forall phi, sat phi = query (compile phi).
Proof. intros [_ H] phi. symmetry. apply H. Qed.

Example size_check :
  length (allInputs (2 ^ 2)) = 16 /\ length (inputsBelow (2 ^ 2)) = 15.
Proof. split; reflexivity. Qed.
