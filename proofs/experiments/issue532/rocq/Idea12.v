(* Issue #532, Idea 12: reduction verification.

   Rocq counterpart of lean/Idea12.lean; theorem names are aligned.

   Many-one reductions f : A -> B from L : A -> bool to M : B -> bool
   (IsReduction f L M := forall x, L x = M (f x)).  Proved in general:
   composition, complement, the constant-map characterisation, trivial
   targets force trivial sources, decider transfer, "yes-to-yes is not
   enough", every L reduces to every nontrivial M if the reduction may
   decide L (so cost bounds are essential), and, in an explicit polynomial
   cost model, transfer of polynomial deciders, composition of polynomial
   reductions and forward transfer of hardness, with explicit constants.

   Verdict: correct tool, insufficient alone.  Nothing here proves or
   refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool.

Section Reductions.
Context {A B C : Type}.

Definition IsReduction (f : A -> B) (L : A -> bool) (M : B -> bool) : Prop :=
  forall x, L x = M (f x).

Definition Nontrivial {T : Type} (L : T -> bool) : Prop :=
  exists a b, L a = true /\ L b = false.

Theorem reduction_id : forall (L : A -> bool), forall x, L x = L (id x).
Proof. intros L x. reflexivity. Qed.

(** Reductions compose. *)
Theorem reduction_comp : forall (f : A -> B) (g : B -> C) L M N,
  IsReduction f L M -> (forall y, M y = N (g y)) -> forall x, L x = N (g (f x)).
Proof. intros f g L M N hf hg x. rewrite hf. apply hg. Qed.

(** A reduction also reduces the complements. *)
Theorem reduction_complement : forall (f : A -> B) L M, IsReduction f L M ->
  IsReduction f (fun x => negb (L x)) (fun y => negb (M y)).
Proof. intros f L M h x. rewrite (h x). reflexivity. Qed.

(** A constant map is a reduction iff L is constant with value M c. *)
Theorem const_reduction_iff : forall L (M : B -> bool) (c : B),
  IsReduction (fun _ : A => c) L M <-> forall x, L x = M c.
Proof. intros L M c. split; intro h; exact h. Qed.

(** A constant map never reduces a nontrivial language. *)
Theorem const_not_reduction : forall L (M : B -> bool), Nontrivial L -> forall c : B,
  ~ IsReduction (fun _ : A => c) L M.
Proof.
  intros L M [a [b [ha hb]]] c h.
  pose proof (h a) as h1. pose proof (h b) as h2. simpl in h1, h2. congruence.
Qed.

(** A reduction into a constant language forces the source to be constant. *)
Theorem trivial_target : forall (f : A -> B) L M (b : bool),
  (forall y, M y = b) -> IsReduction f L M -> forall x, L x = b.
Proof. intros f L M b hM h x. rewrite h. apply hM. Qed.

(** The target of a reduction from a nontrivial language is nontrivial. *)
Theorem nontrivial_target : forall (f : A -> B) L M,
  IsReduction f L M -> Nontrivial L -> Nontrivial M.
Proof.
  intros f L M h [a [b [ha hb]]]. exists (f a), (f b).
  rewrite <- (h a), <- (h b). split; assumption.
Qed.

(** A decider for M that is correct on the image of f gives a decider for L. *)
Theorem decider_transfer : forall (f : A -> B) L M (P : B -> Prop),
  (forall x, P (f x)) -> forall g : B -> bool, (forall y, P y -> g y = M y) ->
  IsReduction f L M -> forall x, g (f x) = L x.
Proof. intros f L M P hP g hg h x. rewrite (hg (f x) (hP x)). symmetry. apply h. Qed.

(** One-directional maps are not reductions. *)
Theorem yes_preserving_not_sufficient : forall L (M : B -> bool), Nontrivial L ->
  forall y, M y = true ->
  (forall x, L x = true -> M ((fun _ : A => y) x) = true) /\
  ~ IsReduction (fun _ : A => y) L M.
Proof.
  intros L M hL y hy. split.
  - intros; exact hy.
  - apply const_not_reduction. exact hL.
Qed.

(** Every language reduces to every nontrivial language when the reduction
    may decide L itself. *)
Theorem reduces_to_any_nontrivial : forall (L : A -> bool) (M : B -> bool),
  Nontrivial M -> exists f : A -> B, IsReduction f L M.
Proof.
  intros L M [a [b [ha hb]]].
  exists (fun x => if L x then a else b). intro x.
  destruct (L x); symmetry; assumption.
Qed.

End Reductions.

(** * Polynomial cost model *)

Record Algo (A B : Type) := mkAlgo { run : A -> B; time : A -> nat }.
Arguments mkAlgo {A B} _ _.
Arguments run {A B} _ _.
Arguments time {A B} _ _.

Definition PolyBounded {A : Type} (sz : A -> nat) (t : A -> nat) : Prop :=
  exists c d, forall x, t x <= c * (sz x + 1) ^ d.

Definition PolyDecider {A : Type} (sz : A -> nat) (L : A -> bool) : Prop :=
  exists D : Algo A bool, (forall x, run D x = L x) /\ PolyBounded sz (time D).

Definition PolyReduction {A B : Type} (szA : A -> nat) (szB : B -> nat)
  (L : A -> bool) (M : B -> bool) (R : Algo A B) : Prop :=
  IsReduction (run R) L M /\
  exists e k, forall x, time R x <= e * (szA x + 1) ^ k /\ szB (run R x) <= e * (szA x + 1) ^ k.

(** Composing polynomial bounds, with explicit constants. *)
Theorem poly_bound_compose : forall n a b e k c d,
  a <= e * (n + 1) ^ k -> b <= c * (a + 1) ^ d ->
  b <= c * (e + 1) ^ d * (n + 1) ^ (k * d).
Proof.
  intros n a b e k c d ha hb.
  pose proof (Nat.pow_le_mono_r (n + 1) 0 k ltac:(lia) ltac:(lia)) as hpos.
  simpl in hpos.
  assert (h1 : a + 1 <= (e + 1) * (n + 1) ^ k) by nia.
  pose proof (Nat.pow_le_mono_l _ _ d h1) as h2.
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in h2.
  rewrite <- Nat.mul_assoc.
  eapply Nat.le_trans; [exact hb|]. apply Nat.mul_le_mono_l. exact h2.
Qed.

(** Summing two polynomial bounds into one. *)
Theorem poly_sum_bound : forall n e k Cst d,
  e * (n + 1) ^ k + Cst * (n + 1) ^ (k * d) <= (e + Cst) * (n + 1) ^ (k * d + k).
Proof.
  intros n e k Cst d.
  pose proof (Nat.pow_le_mono_r (n + 1) k (k * d + k) ltac:(lia) ltac:(lia)) as h1.
  pose proof (Nat.pow_le_mono_r (n + 1) (k * d) (k * d + k) ltac:(lia) ltac:(lia)) as h2.
  rewrite Nat.mul_add_distr_r.
  apply Nat.add_le_mono; apply Nat.mul_le_mono_l; assumption.
Qed.

(** Polynomial deciders pull back along polynomial reductions. *)
Theorem poly_decider_transfer : forall {A B : Type} (szA : A -> nat) (szB : B -> nat) L M
  (R : Algo A B), PolyReduction szA szB L M R -> PolyDecider szB M -> PolyDecider szA L.
Proof.
  intros A B szA szB L M R [hred [e [k hek]]] [D [hD [c [d hcd]]]].
  exists (mkAlgo (fun x => run D (run R x)) (fun x => time R x + time D (run R x))).
  split.
  - intro x. simpl. rewrite hD. symmetry. apply hred.
  - exists (e + c * (e + 1) ^ d), (k * d + k). intro x. simpl.
    destruct (hek x) as [h1 hz].
    pose proof (poly_bound_compose (szA x) (szB (run R x)) (time D (run R x)) e k c d hz (hcd _)) as h2.
    pose proof (poly_sum_bound (szA x) e k (c * (e + 1) ^ d) d) as h3.
    lia.
Qed.

(** Polynomial reductions compose. *)
Theorem poly_reduction_comp : forall {A B C : Type} (szA : A -> nat) (szB : B -> nat)
  (szC : C -> nat) L M N (R : Algo A B) (S : Algo B C),
  PolyReduction szA szB L M R -> PolyReduction szB szC M N S ->
  PolyReduction szA szC L N (mkAlgo (fun x => run S (run R x)) (fun x => time R x + time S (run R x))).
Proof.
  intros A B C szA szB szC L M N R S [hr [e [k hek]]] [hs [e' [k' hek']]].
  split.
  - intro x. simpl. rewrite (hr x). apply hs.
  - exists (e + e' * (e + 1) ^ k'), (k * k' + k). intro x. simpl.
    destruct (hek x) as [h1 hz]. destruct (hek' (run R x)) as [ht' hz'].
    pose proof (poly_sum_bound (szA x) e k (e' * (e + 1) ^ k') k') as h3.
    pose proof (poly_bound_compose (szA x) (szB (run R x)) (time S (run R x)) e k e' k' hz ht') as ht.
    pose proof (poly_bound_compose (szA x) (szB (run R x)) (szC (run S (run R x))) e k e' k' hz hz') as hc.
    split; lia.
Qed.

(** Hardness transfers forward along polynomial reductions. *)
Theorem hardness_transfer : forall {A B : Type} (szA : A -> nat) (szB : B -> nat) L M
  (R : Algo A B), PolyReduction szA szB L M R -> ~ PolyDecider szA L -> ~ PolyDecider szB M.
Proof.
  intros A B szA szB L M R hR hL hM. apply hL. exact (poly_decider_transfer szA szB L M R hR hM).
Qed.
