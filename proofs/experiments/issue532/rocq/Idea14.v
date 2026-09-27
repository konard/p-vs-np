(* Issue #532, Idea 14: randomized search.

   Rocq counterpart of lean/Idea14.lean; theorem names are aligned.

   A randomized algorithm on input x is a function A x : nat -> bool of a
   seed i < s x.  cnt s P counts seeds i < s with P i; countT s k Q counts
   length-k seed tuples over [0, s) satisfying Q by honest enumeration.
   Proved in general: s^k tuples (countT_true), (cnt s P)^k all-P tuples
   (countT_all), one-sided amplification (amplification_count,
   rp_amplification, one_sided_amplified), observed success is no guarantee
   (observed_success_no_guarantee), derandomization by seed enumeration and
   its cost (enumeration_decides, poly_seeds_derandomize,
   polySeedRP_implies_poly), and the conditional theorem
   rp_sat_with_seed_compression.

   Verdict: randomness changes the target class; returning to P needs an
   open derandomization step.  NPinRP and SeedCompression are definitions,
   never assumed.  Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.

Fixpoint sumTo (n : nat) (f : nat -> nat) : nat :=
  match n with 0 => 0 | S m => sumTo m f + f m end.

Definition cnt (s : nat) (P : nat -> bool) : nat := sumTo s (fun i => if P i then 1 else 0).

Fixpoint countT (s k : nat) (Q : list nat -> bool) : nat :=
  match k with
  | 0 => if Q [] then 1 else 0
  | S k' => sumTo s (fun i => countT s k' (fun t => Q (i :: t)))
  end.

Lemma sumTo_ext : forall n f g, (forall i, f i = g i) -> sumTo n f = sumTo n g.
Proof. induction n; intros f g h; simpl; [reflexivity|]. rewrite (IHn f g h), h. reflexivity. Qed.

Lemma countT_ext : forall s k Q Q', (forall t, Q t = Q' t) -> countT s k Q = countT s k Q'.
Proof.
  intros s k. induction k; intros Q Q' h; simpl.
  - rewrite h. reflexivity.
  - apply sumTo_ext. intro i. apply IHk. intro t. apply h.
Qed.

Lemma sumTo_const : forall s X, sumTo s (fun _ => X) = s * X.
Proof. induction s; intro X; simpl; [reflexivity|]. rewrite IHs. lia. Qed.

Lemma sumTo_ite_mul : forall s X (P : nat -> bool),
  sumTo s (fun i => if P i then X else 0) = cnt s P * X.
Proof.
  intros s X P. unfold cnt. induction s; simpl; [reflexivity|].
  rewrite IHs, Nat.mul_add_distr_r. destruct (P s); lia.
Qed.

Lemma countT_false : forall s k, countT s k (fun _ => false) = 0.
Proof.
  intros s k. induction k; simpl; [reflexivity|].
  rewrite (sumTo_ext s _ (fun _ => 0)); [rewrite sumTo_const; lia|].
  intro i. exact IHk.
Qed.

(** There are exactly s^k tuples of length k. *)
Theorem countT_true : forall s k, countT s k (fun _ => true) = s ^ k.
Proof.
  intros s k. induction k; simpl; [reflexivity|].
  rewrite (sumTo_ext s _ (fun _ => s ^ k)); [rewrite sumTo_const; reflexivity|].
  intro i. exact IHk.
Qed.

(** Exactly (cnt s P)^k tuples consist only of seeds satisfying P. *)
Theorem countT_all : forall s k (P : nat -> bool),
  countT s k (fun t => forallb P t) = cnt s P ^ k.
Proof.
  intros s k P. induction k; simpl; [reflexivity|].
  rewrite (sumTo_ext s _ (fun i => if P i then countT s k (fun t => forallb P t) else 0)).
  - rewrite sumTo_ite_mul, IHk. lia.
  - intro i. destruct (P i) eqn:hi.
    + apply countT_ext. intro t. simpl. try rewrite hi. reflexivity.
    + rewrite <- (countT_false s k). apply countT_ext. intro t. simpl. try rewrite hi. reflexivity.
Qed.

(** Amplification arithmetic: 2b <= s implies b^k * 2^k <= s^k. *)
Theorem amplification_count : forall b s k, 2 * b <= s -> b ^ k * 2 ^ k <= s ^ k.
Proof.
  intros b s k h. rewrite <- Nat.pow_mul_l. apply Nat.pow_le_mono_l. lia.
Qed.

Lemma not_any_eq_all : forall (A : nat -> bool) t,
  negb (existsb A t) = forallb (fun i => negb (A i)) t.
Proof.
  intros A t. induction t as [|a t IH]; simpl; [reflexivity|].
  rewrite negb_orb, IH. reflexivity.
Qed.

(** One-sided amplification. *)
Theorem rp_amplification : forall (A : nat -> bool) s k,
  2 * cnt s (fun i => negb (A i)) <= s ->
  countT s k (fun t => negb (existsb A t)) * 2 ^ k <= s ^ k.
Proof.
  intros A s k h.
  rewrite (countT_ext s k _ (fun t => forallb (fun i => negb (A i)) t)).
  - rewrite countT_all. apply amplification_count. exact h.
  - intro t. apply not_any_eq_all.
Qed.

Lemma cnt_compl : forall s (P : nat -> bool), cnt s P + cnt s (fun i => negb (P i)) = s.
Proof.
  intros s P. unfold cnt. induction s; simpl; [reflexivity|].
  destruct (P s); simpl; lia.
Qed.

(** Boolean membership of a seed in a list. *)
Fixpoint memB (i : nat) (l : list nat) : bool :=
  match l with [] => false | a :: l' => Nat.eqb i a || memB i l' end.

Lemma cnt_eq_le : forall s a, cnt s (fun i => Nat.eqb i a) <= 1.
Proof.
  intros s a.
  assert (H : cnt s (fun i => Nat.eqb i a) = if Nat.ltb a s then 1 else 0).
  { unfold cnt. induction s; simpl; [reflexivity|]. rewrite IHs.
    destruct (Nat.ltb_spec a s); destruct (Nat.eqb_spec s a);
      destruct (Nat.ltb_spec a (S s)); lia. }
  rewrite H. destruct (Nat.ltb a s); lia.
Qed.

Lemma cnt_or_le : forall s (P Q : nat -> bool),
  cnt s (fun i => P i || Q i) <= cnt s P + cnt s Q.
Proof.
  intros s P Q. unfold cnt. induction s; simpl; [lia|].
  destruct (P s), (Q s); simpl; lia.
Qed.

Lemma cnt_memB_le : forall s obs, cnt s (fun i => memB i obs) <= length obs.
Proof.
  intros s obs. induction obs as [|a l IH]; simpl.
  - unfold cnt. simpl. rewrite sumTo_const. lia.
  - pose proof (cnt_or_le s (fun i => Nat.eqb i a) (fun i => memB i l)).
    pose proof (cnt_eq_le s a). lia.
Qed.

(** Observed success is no guarantee. *)
Theorem observed_success_no_guarantee : forall (obs : list nat) s,
  exists A : nat -> bool, (forall i, In i obs -> A i = true) /\
    s <= cnt s (fun i => negb (A i)) + length obs.
Proof.
  intros obs s. exists (fun i => memB i obs). split.
  - intros i hi. induction obs as [|a l IH]; simpl in *; [contradiction|].
    destruct hi as [e | h].
    + subst. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (IH h). apply orb_true_r.
  - pose proof (cnt_compl s (fun i => memB i obs)).
    pose proof (cnt_memB_le s obs). lia.
Qed.

(** One-sided error. *)
Definition OneSided {T : Type} (L : T -> bool) (A : T -> nat -> bool) (s : T -> nat) : Prop :=
  forall x, 0 < s x /\ (L x = false -> forall i, A x i = false) /\
    (L x = true -> 2 * cnt (s x) (fun i => negb (A x i)) <= s x).

Fixpoint anySeed (n : nat) (f : nat -> bool) : bool :=
  match n with 0 => false | S m => anySeed m f || f m end.

Lemma anySeed_false : forall s f, (forall i, f i = false) -> anySeed s f = false.
Proof. induction s; intros f h; simpl; [reflexivity|]. rewrite IHs, h; auto. Qed.

Lemma anySeed_cnt : forall s f, anySeed s f = false -> cnt s f = 0.
Proof.
  intros s f. unfold cnt. induction s; simpl; intro h; [reflexivity|].
  apply orb_false_iff in h. destruct h as [h1 h2]. rewrite IHs, h2; auto.
Qed.

(** One-sided amplification for a whole algorithm. *)
Theorem one_sided_amplified : forall {T : Type} (L : T -> bool) (A : T -> nat -> bool) (s : T -> nat),
  OneSided L A s -> forall x k,
  (L x = false -> forall t, existsb (A x) t = false) /\
  (L x = true -> countT (s x) k (fun t => negb (existsb (A x) t)) * 2 ^ k <= s x ^ k).
Proof.
  intros T L A s hA x k. destruct (hA x) as [_ [hno hyes]]. split.
  - intros h t. induction t as [|a t IH]; simpl; [reflexivity|]. rewrite (hno h a), IH. reflexivity.
  - intro h. apply rp_amplification. exact (hyes h).
Qed.

(** Derandomization by enumerating all seeds is correct. *)
Theorem enumeration_decides : forall {T : Type} (L : T -> bool) (A : T -> nat -> bool) (s : T -> nat),
  OneSided L A s -> forall x, anySeed (s x) (A x) = L x.
Proof.
  intros T L A s hA x. destruct (hA x) as [hpos [hno hyes]].
  destruct (L x) eqn:hL.
  - destruct (anySeed (s x) (A x)) eqn:he; [reflexivity|].
    pose proof (anySeed_cnt _ _ he). pose proof (cnt_compl (s x) (A x)).
    pose proof (hyes eq_refl). lia.
  - apply anySeed_false. apply hno. reflexivity.
Qed.

(** Enumeration is polynomial when the seed space is. *)
Theorem poly_seeds_derandomize : forall {T : Type} (sz : T -> nat) (L : T -> bool)
  (A : T -> nat -> bool) (s Tm : T -> nat) (c d e k : nat),
  OneSided L A s -> (forall x, s x <= e * (sz x + 1) ^ k) ->
  (forall x, Tm x <= c * (sz x + 1) ^ d) ->
  forall x, anySeed (s x) (A x) = L x /\ s x * Tm x <= e * c * (sz x + 1) ^ (k + d).
Proof.
  intros T sz L A s Tm c d e k hA hs hT x. split.
  - apply enumeration_decides. exact hA.
  - pose proof (Nat.mul_le_mono _ _ _ _ (hs x) (hT x)) as h.
    rewrite Nat.pow_add_r.
    replace (e * c * ((sz x + 1) ^ k * (sz x + 1) ^ d))
      with (e * (sz x + 1) ^ k * (c * (sz x + 1) ^ d)) by ring.
    exact h.
Qed.

Definition PolyDec {T : Type} (sz : T -> nat) (L : T -> bool) : Prop :=
  exists (D : T -> bool) (t : T -> nat) (c d : nat),
    (forall x, D x = L x) /\ forall x, t x <= c * (sz x + 1) ^ d.

Definition RPDecider {T : Type} (sz : T -> nat) (L : T -> bool) : Prop :=
  exists (A : T -> nat -> bool) (r Tm : T -> nat) (c d : nat),
    OneSided L A (fun x => 2 ^ r x) /\
    forall x, r x <= c * (sz x + 1) ^ d /\ Tm x <= c * (sz x + 1) ^ d.

Definition PolySeedRP {T : Type} (sz : T -> nat) (L : T -> bool) : Prop :=
  exists (A : T -> nat -> bool) (s Tm : T -> nat) (c d : nat),
    OneSided L A s /\ forall x, s x <= c * (sz x + 1) ^ d /\ Tm x <= c * (sz x + 1) ^ d.

(** Polynomially many seeds can be enumerated deterministically. *)
Theorem polySeedRP_implies_poly : forall {T : Type} (sz : T -> nat) (L : T -> bool),
  PolySeedRP sz L -> PolyDec sz L.
Proof.
  intros T sz L [A [s [Tm [c [d [hA hb]]]]]].
  exists (fun x => anySeed (s x) (A x)), (fun x => s x * Tm x), (c * c), (d + d). split.
  - intro x. apply enumeration_decides. exact hA.
  - intro x.
    exact (proj2 (poly_seeds_derandomize sz L A s Tm c d c d hA
      (fun y => proj1 (hb y)) (fun y => proj2 (hb y)) x)).
Qed.

(** Open obligation (not assumed). *)
Definition NPinRP {T : Type} (sz : T -> nat) (L : T -> bool) : Prop := RPDecider sz L.

(** Open obligation (not assumed): seed compression. *)
Definition SeedCompression {T : Type} (sz : T -> nat) (L : T -> bool) : Prop :=
  RPDecider sz L -> PolySeedRP sz L.

(** Conditional theorem. *)
Theorem rp_sat_with_seed_compression : forall {T : Type} (sz : T -> nat) (L : T -> bool),
  NPinRP sz L -> SeedCompression sz L -> PolyDec sz L.
Proof. intros T sz L h1 h2. apply polySeedRP_implies_poly. apply h2. exact h1. Qed.
