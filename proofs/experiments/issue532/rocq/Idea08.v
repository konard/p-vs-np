(* Issue #532, Idea 08: program induction and generalization from finite
   examples.

   Proved for all parameters:
   - two_consistent_extensions: for every consistent finite sample S and every
     unobserved input x, two total functions consistent with S disagree at x;
   - all_patterns_consistent, realised_patterns: for k distinct unobserved
     inputs, each of the 2^k bit patterns on them is realised by a function
     consistent with S;
   - lookup_consistent: the lookup table fits every consistent sample;
   - elimination_identifies: with a finite class H containing the target and
     separating inputs, every survivor of consistent elimination equals the
     target; no_separation_unrestricted: for all functions, no finite sample
     separates.

   Verdict: refuted as a route (general theorem). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Definition Consistent (f : nat -> bool) (S : list (nat * bool)) : Prop :=
  forall p, In p S -> f (fst p) = snd p.

Definition SampleConsistent (S : list (nat * bool)) : Prop :=
  exists f : nat -> bool, Consistent f S.

Definition inputs (S : list (nat * bool)) : list nat := map fst S.

Lemma not_mem_inputs (S : list (nat * bool)) (x : nat) :
  ~ In x (inputs S) -> forall p, In p S -> fst p <> x.
Proof.
  intros Hx p Hp E. apply Hx. unfold inputs. apply in_map_iff.
  exists p; split; auto.
Qed.

Definition override (f0 : nat -> bool) (x : nat) (b : bool) (y : nat) : bool :=
  if Nat.eqb y x then b else f0 y.

Theorem two_consistent_extensions (S : list (nat * bool)) (x : nat) :
  SampleConsistent S -> ~ In x (inputs S) ->
  exists f g : nat -> bool, Consistent f S /\ Consistent g S /\ f x <> g x.
Proof.
  intros [f0 Hf0] Hx.
  exists (override f0 x true), (override f0 x false). repeat split.
  - intros p Hp. unfold override.
    destruct (Nat.eqb (fst p) x) eqn:E.
    + apply Nat.eqb_eq in E. exfalso; exact (not_mem_inputs S x Hx p Hp E).
    + apply Hf0; exact Hp.
  - intros p Hp. unfold override.
    destruct (Nat.eqb (fst p) x) eqn:E.
    + apply Nat.eqb_eq in E. exfalso; exact (not_mem_inputs S x Hx p Hp E).
    + apply Hf0; exact Hp.
  - unfold override. rewrite Nat.eqb_refl. discriminate.
Qed.

Fixpoint ext (f0 : nat -> bool) (U : list nat) (m : list bool) (y : nat) : bool :=
  match U, m with
  | u :: U', b :: m' => if Nat.eqb y u then b else ext f0 U' m' y
  | _, _ => f0 y
  end.

Lemma ext_outside (f0 : nat -> bool) (U : list nat) (m : list bool) (y : nat) :
  ~ In y U -> ext f0 U m y = f0 y.
Proof.
  revert m; induction U as [|u U IH]; intros m Hy; destruct m as [|b m]; simpl; auto.
  destruct (Nat.eqb y u) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso; apply Hy; simpl; auto.
  - apply IH. intros H; apply Hy; simpl; auto.
Qed.

Lemma ext_pattern (f0 : nat -> bool) (U : list nat) (m : list bool) :
  NoDup U -> length m = length U -> map (ext f0 U m) U = m.
Proof.
  revert m; induction U as [|u U IH]; intros m HU Hm; destruct m as [|b m];
    simpl in *; try discriminate; auto.
  inversion HU; subst.
  rewrite Nat.eqb_refl. f_equal.
  transitivity (map (ext f0 U m) U); [|apply IH; auto].
  apply map_ext_in. intros y Hy.
  destruct (Nat.eqb y u) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Theorem all_patterns_consistent (S : list (nat * bool)) (U : list nat) (m : list bool) :
  SampleConsistent S -> NoDup U -> (forall u, In u U -> ~ In u (inputs S)) ->
  length m = length U ->
  exists f : nat -> bool, Consistent f S /\ map f U = m.
Proof.
  intros [f0 Hf0] HU Hdisj Hm.
  exists (ext f0 U m). split; [|apply ext_pattern; auto].
  intros p Hp.
  assert (Hp' : ~ In (fst p) U).
  { intros Hin. apply (Hdisj (fst p) Hin). unfold inputs. apply in_map_iff.
    exists p; split; auto. }
  rewrite ext_outside; auto.
Qed.

Fixpoint allStrings (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allStrings n') ++ map (cons true) (allStrings n')
  end.

Theorem length_allStrings (n : nat) : length (allStrings n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allStrings_iff (n : nat) (v : list bool) :
  In v (allStrings n) <-> length v = n.
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

Theorem realised_patterns (S : list (nat * bool)) (U : list nat) :
  SampleConsistent S -> NoDup U -> (forall u, In u U -> ~ In u (inputs S)) ->
  length (allStrings (length U)) = 2 ^ length U /\
  forall m, In m (allStrings (length U)) ->
    exists f : nat -> bool, Consistent f S /\ map f U = m.
Proof.
  intros HS HU Hdisj. split; [apply length_allStrings|].
  intros m Hm. apply all_patterns_consistent; auto.
  apply mem_allStrings_iff; exact Hm.
Qed.

Fixpoint lookup (S : list (nat * bool)) (y : nat) : bool :=
  match S with
  | [] => false
  | (a, b) :: S' => if Nat.eqb y a then b else lookup S' y
  end.

Theorem lookup_consistent (S : list (nat * bool)) :
  SampleConsistent S -> Consistent (lookup S) S.
Proof.
  intros [f0 Hf0]. induction S as [|[a b] S IH]; intros p Hp; [contradiction|].
  assert (Hq : f0 a = b) by (apply (Hf0 (a, b)); simpl; auto).
  destruct Hp as [Hp|Hp].
  - subst p. simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. destruct (Nat.eqb (fst p) a) eqn:E.
    + apply Nat.eqb_eq in E. rewrite <- Hq, <- E. apply Hf0; simpl; auto.
    + apply IH; auto. intros q Hq'; apply Hf0; simpl; auto.
Qed.

Definition labelWith (t : nat -> bool) (xs : list nat) : list (nat * bool) :=
  map (fun x => (x, t x)) xs.

Definition survivors (H : list (nat -> bool)) (S : list (nat * bool)) :
  list (nat -> bool) :=
  filter (fun h => forallb (fun p => Bool.eqb (h (fst p)) (snd p)) S) H.

Definition Separates (xs : list nat) (H : list (nat -> bool)) : Prop :=
  forall h h', In h H -> In h' H -> (forall x, In x xs -> h x = h' x) ->
  forall y, h y = h' y.

Theorem mem_survivors (H : list (nat -> bool)) (t : nat -> bool) (xs : list nat)
  (h : nat -> bool) :
  In h (survivors H (labelWith t xs)) <-> In h H /\ forall x, In x xs -> h x = t x.
Proof.
  unfold survivors, labelWith. rewrite filter_In, forallb_forall. split.
  - intros [HH Hall]. split; auto. intros x Hx.
    assert (In (x, t x) (map (fun x => (x, t x)) xs)) as Hin
      by (apply in_map_iff; exists x; auto).
    specialize (Hall _ Hin). simpl in Hall. apply Bool.eqb_prop in Hall. exact Hall.
  - intros [HH Hall]. split; auto. intros p Hp.
    apply in_map_iff in Hp. destruct Hp as [x [Hx Hin]]. subst p. simpl.
    rewrite (Hall x Hin). apply Bool.eqb_reflx.
Qed.

Theorem elimination_identifies (H : list (nat -> bool)) (t : nat -> bool) (xs : list nat) :
  In t H -> Separates xs H ->
  In t (survivors H (labelWith t xs)) /\
  forall h, In h (survivors H (labelWith t xs)) -> forall y, h y = t y.
Proof.
  intros Ht Hsep. split.
  - apply mem_survivors. split; auto.
  - intros h Hh y. apply mem_survivors in Hh. destruct Hh as [HH Hagree].
    exact (Hsep h t HH Ht Hagree y).
Qed.

Theorem no_separation_unrestricted (xs : list nat) (x : nat) (f0 : nat -> bool) :
  ~ In x xs ->
  exists f g : nat -> bool, (forall y, In y xs -> f y = g y) /\ f x <> g x.
Proof.
  intros Hx. exists (override f0 x true), (override f0 x false). split.
  - intros y Hy. unfold override. destruct (Nat.eqb y x) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction.
  - unfold override. rewrite Nat.eqb_refl. discriminate.
Qed.
