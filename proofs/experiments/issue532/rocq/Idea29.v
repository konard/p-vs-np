(* Issue #532, Idea 29: reduction chains and polynomial composition.

   Verdict: correct tool, insufficient alone (general theorem proved).

   Explicit polynomials coefficient * (n + 1) ^ degree are closed under
   addition and substitution, so polynomially bounded many-one reductions
   compose (time, output size, and correctness), and polynomial-time
   decidability is inherited backwards along reductions.  The theorem
   reducesToP_iff_inP shows that reducing L to some polynomial-time language
   is equivalent to L being polynomial-time: the obligation of a "reduce NP to
   P" argument is exactly the goal.  Nothing here decides P vs NP.
   Standalone; running time is an abstract cost function. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Record Poly := mkPoly { coefficient : nat; degree : nat }.

Definition eval (p : Poly) (n : nat) : nat :=
  coefficient p * (n + 1) ^ degree p.

Definition poly_add (p q : Poly) : Poly :=
  mkPoly (coefficient p + coefficient q) (Nat.max (degree p) (degree q)).

Definition poly_comp (p q : Poly) : Poly :=
  mkPoly (coefficient q * (coefficient p + 1) ^ degree q) (degree p * degree q).

Definition poly_linear : Poly := mkPoly 1 1.
Definition poly_zero : Poly := mkPoly 0 0.

Lemma pow_pos_succ (n k : nat) : 1 <= (n + 1) ^ k.
Proof.
  assert (H : (n + 1) ^ k <> 0) by (apply Nat.pow_nonzero; lia). lia.
Qed.

(* Explicit polynomials are monotone in the input length. *)
Theorem eval_mono (p : Poly) (m n : nat) : m <= n -> eval p m <= eval p n.
Proof.
  intro H. unfold eval. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. lia.
Qed.

(* Closure under addition. *)
Theorem add_bound (p q : Poly) (n : nat) :
  eval p n + eval q n <= eval (poly_add p q) n.
Proof.
  unfold eval, poly_add; simpl.
  assert (hp : (n + 1) ^ degree p <= (n + 1) ^ Nat.max (degree p) (degree q))
    by (apply Nat.pow_le_mono_r; [lia | apply Nat.le_max_l]).
  assert (hq : (n + 1) ^ degree q <= (n + 1) ^ Nat.max (degree p) (degree q))
    by (apply Nat.pow_le_mono_r; [lia | apply Nat.le_max_r]).
  rewrite Nat.mul_add_distr_r.
  apply Nat.add_le_mono; apply Nat.mul_le_mono_l; assumption.
Qed.

(* Closure under composition: q (p n) <= (poly_comp p q) n. *)
Theorem comp_bound (p q : Poly) (n : nat) :
  eval q (eval p n) <= eval (poly_comp p q) n.
Proof.
  unfold eval, poly_comp; simpl.
  pose proof (pow_pos_succ n (degree p)) as hX.
  assert (h1 : coefficient p * (n + 1) ^ degree p + 1
               <= (coefficient p + 1) * (n + 1) ^ degree p) by lia.
  assert (h2 : (coefficient p * (n + 1) ^ degree p + 1) ^ degree q
               <= ((coefficient p + 1) * (n + 1) ^ degree p) ^ degree q)
    by (apply Nat.pow_le_mono_l; exact h1).
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in h2.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. exact h2.
Qed.

Theorem poly_comp_exists (p q : Poly) :
  exists r : Poly, forall n, eval q (eval p n) <= eval r n.
Proof. exists (poly_comp p q). apply comp_bound. Qed.

Theorem poly_add_exists (p q : Poly) :
  exists r : Poly, forall n, eval p n + eval q n <= eval r n.
Proof. exists (poly_add p q). apply add_bound. Qed.

Definition IsReduction {A B : Type} (f : A -> B) (L : A -> Prop) (M : B -> Prop) : Prop :=
  forall x, L x <-> M (f x).

(* Correctness of reductions composes. *)
Theorem reduction_comp {A B C : Type} (f : A -> B) (g : B -> C)
  (L : A -> Prop) (M : B -> Prop) (N : C -> Prop) :
  IsReduction f L M -> IsReduction g M N -> IsReduction (fun x => g (f x)) L N.
Proof.
  intros hf hg x. rewrite (hf x). apply hg.
Qed.

Theorem reduction_id {A : Type} (L : A -> Prop) : IsReduction (fun x => x) L L.
Proof. intro x. reflexivity. Qed.

Record PolyMap {A B : Type} (sa : A -> nat) (sb : B -> nat) := mkPolyMap {
  pm_fn : A -> B;
  pm_time : A -> nat;
  pm_timeBound : Poly;
  pm_sizeBound : Poly;
  pm_time_le : forall x, pm_time x <= eval pm_timeBound (sa x);
  pm_size_le : forall x, sb (pm_fn x) <= eval pm_sizeBound (sa x)
}.
Arguments mkPolyMap {A B sa sb}.
Arguments pm_fn {A B sa sb}.
Arguments pm_time {A B sa sb}.
Arguments pm_timeBound {A B sa sb}.
Arguments pm_sizeBound {A B sa sb}.
Arguments pm_time_le {A B sa sb}.
Arguments pm_size_le {A B sa sb}.

(* Running f then g: time is the sum, bounds are explicit. *)
Definition polymap_comp {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  (f : PolyMap sa sb) (g : PolyMap sb sc) : PolyMap sa sc.
Proof.
  refine (mkPolyMap (fun x => pm_fn g (pm_fn f x))
    (fun x => pm_time f x + pm_time g (pm_fn f x))
    (poly_add (pm_timeBound f) (poly_comp (pm_sizeBound f) (pm_timeBound g)))
    (poly_comp (pm_sizeBound f) (pm_sizeBound g)) _ _).
  - intro x.
    pose proof (pm_time_le f x) as h1.
    pose proof (pm_time_le g (pm_fn f x)) as h2.
    pose proof (eval_mono (pm_timeBound g) _ _ (pm_size_le f x)) as h2'.
    pose proof (comp_bound (pm_sizeBound f) (pm_timeBound g) (sa x)) as h3.
    pose proof (add_bound (pm_timeBound f)
      (poly_comp (pm_sizeBound f) (pm_timeBound g)) (sa x)) as h4.
    lia.
  - intro x.
    pose proof (pm_size_le g (pm_fn f x)) as h1.
    pose proof (eval_mono (pm_sizeBound g) _ _ (pm_size_le f x)) as h2.
    pose proof (comp_bound (pm_sizeBound f) (pm_sizeBound g) (sa x)) as h3.
    lia.
Defined.

(* The time of a composed chain of polynomially bounded maps is polynomial. *)
Theorem comp_time_poly {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  (f : PolyMap sa sb) (g : PolyMap sb sc) :
  exists r : Poly, forall x, pm_time f x + pm_time g (pm_fn f x) <= eval r (sa x).
Proof.
  exists (pm_timeBound (polymap_comp f g)). intro x.
  exact (pm_time_le (polymap_comp f g) x).
Qed.

Definition polymap_ident {A : Type} (sa : A -> nat) : PolyMap sa sa.
Proof.
  refine (mkPolyMap (fun x => x) (fun _ => 0) poly_zero poly_linear _ _).
  - intro x. lia.
  - intro x. unfold eval, poly_linear; simpl. lia.
Defined.

Record PolyReduction {A B : Type} (sa : A -> nat) (sb : B -> nat)
  (L : A -> Prop) (M : B -> Prop) := mkPolyReduction {
  pr_map : PolyMap sa sb;
  pr_correct : IsReduction (pm_fn pr_map) L M
}.
Arguments mkPolyReduction {A B sa sb L M}.
Arguments pr_map {A B sa sb L M}.
Arguments pr_correct {A B sa sb L M}.

(* Polynomially bounded reductions compose. *)
Definition polyred_comp {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  {L : A -> Prop} {M : B -> Prop} {N : C -> Prop}
  (f : PolyReduction sa sb L M) (g : PolyReduction sb sc M N) :
  PolyReduction sa sc L N :=
  mkPolyReduction (polymap_comp (pr_map f) (pr_map g))
    (reduction_comp _ _ L M N (pr_correct f) (pr_correct g)).

(* The composed reduction computes g after f. *)
Theorem polyred_comp_fn {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  {L : A -> Prop} {M : B -> Prop} {N : C -> Prop}
  (f : PolyReduction sa sb L M) (g : PolyReduction sb sc M N) :
  forall x, pm_fn (pr_map (polyred_comp f g)) x = pm_fn (pr_map g) (pm_fn (pr_map f) x).
Proof. reflexivity. Qed.

Record PolyDecider {A : Type} (sa : A -> nat) (L : A -> Prop) := mkPolyDecider {
  pd_decide : A -> bool;
  pd_time : A -> nat;
  pd_bound : Poly;
  pd_correct : forall x, L x <-> pd_decide x = true;
  pd_time_le : forall x, pd_time x <= eval pd_bound (sa x)
}.
Arguments mkPolyDecider {A sa L}.
Arguments pd_decide {A sa L}.
Arguments pd_time {A sa L}.
Arguments pd_bound {A sa L}.
Arguments pd_correct {A sa L}.
Arguments pd_time_le {A sa L}.

Definition InP {A : Type} (sa : A -> nat) (L : A -> Prop) : Prop :=
  inhabited (PolyDecider sa L).

(* Pull a decider back along a polynomially bounded reduction. *)
Definition pullback {A B : Type} {sa : A -> nat} {sb : B -> nat}
  {L : A -> Prop} {M : B -> Prop}
  (r : PolyReduction sa sb L M) (d : PolyDecider sb M) : PolyDecider sa L.
Proof.
  refine (mkPolyDecider (fun x => pd_decide d (pm_fn (pr_map r) x))
    (fun x => pm_time (pr_map r) x + pd_time d (pm_fn (pr_map r) x))
    (poly_add (pm_timeBound (pr_map r))
      (poly_comp (pm_sizeBound (pr_map r)) (pd_bound d))) _ _).
  - intro x. rewrite (pr_correct r x). apply (pd_correct d).
  - intro x.
    pose proof (pm_time_le (pr_map r) x) as h1.
    pose proof (pd_time_le d (pm_fn (pr_map r) x)) as h2.
    pose proof (eval_mono (pd_bound d) _ _ (pm_size_le (pr_map r) x)) as h2'.
    pose proof (comp_bound (pm_sizeBound (pr_map r)) (pd_bound d) (sa x)) as h3.
    pose proof (add_bound (pm_timeBound (pr_map r))
      (poly_comp (pm_sizeBound (pr_map r)) (pd_bound d)) (sa x)) as h4.
    lia.
Defined.

(* The polynomial-time class is closed backwards under polynomial reductions. *)
Theorem inP_of_reduction {A B : Type} {sa : A -> nat} {sb : B -> nat}
  {L : A -> Prop} {M : B -> Prop}
  (r : PolyReduction sa sb L M) : InP sb M -> InP sa L.
Proof. intros [d]. exact (inhabits (pullback r d)). Qed.

Definition ClosedUnderReductions {A : Type} (sa : A -> nat)
  (C : (A -> Prop) -> Prop) : Prop :=
  forall L M, inhabited (PolyReduction sa sa L M) -> C M -> C L.

Theorem inP_closed {A : Type} (sa : A -> nat) : ClosedUnderReductions sa (InP sa).
Proof. intros L M [r] hM. exact (inP_of_reduction r hM). Qed.

(* A closed class containing a complete language contains the whole family. *)
Theorem closed_contains_family {A : Type} (sa : A -> nat) (C : (A -> Prop) -> Prop)
  (hC : ClosedUnderReductions sa C) (family : (A -> Prop) -> Prop) (K : A -> Prop)
  (hard : forall L, family L -> inhabited (PolyReduction sa sa L K)) (hK : C K) :
  forall L, family L -> C L.
Proof. intros L hL. exact (hC L K (hard L hL) hK). Qed.

(* Open obligation of any "reduce L to an easy problem" argument. *)
Definition ReducesToP {A : Type} (sa : A -> nat) (L : A -> Prop) : Prop :=
  exists (B : Type) (sb : B -> nat) (M : B -> Prop),
    inhabited (PolyReduction sa sb L M) /\ InP sb M.

(* The obligation is exactly as hard as the goal. *)
Theorem reducesToP_iff_inP {A : Type} (sa : A -> nat) (L : A -> Prop) :
  ReducesToP sa L <-> InP sa L.
Proof.
  split.
  - intros [B [sb [M [[r] hM]]]]. exact (inP_of_reduction r hM).
  - intro h. exists A, sa, L. split; [| exact h].
    exact (inhabits (mkPolyReduction (polymap_ident sa) (reduction_id L))).
Qed.
