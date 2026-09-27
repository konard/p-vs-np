(* Issue #532, Idea 39: proof-system scope (lower bounds and p-simulation).

   Rocq counterpart of ../lean/Idea39.lean (same theorem names and content).
   Abstract Cook-Reckhow setting: a proof system over formulas F is a relation
   Proves : Proof -> F -> Prop with size : Proof -> nat; polynomials are pairs
   (c, k) evaluated as c * (n + 1) ^ k. Lower bounds transfer downward along
   p-simulation (superpoly_transfer), short proofs transfer upward
   (poly_bounded_transfer), p-simulation is a preorder (psim_refl, psim_trans),
   and a general countermodel (weak_lb_strong_short) shows that a lower bound for
   a weak system is consistent with short proofs in a stronger one. The open
   obligation SuperpolyAllSystems is equivalent to NP <> coNP for Cook-Reckhow
   systems (Cook-Reckhow 1979; not formalized). All proofs are constructive. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.

Theorem tested :
  exists weak strong : bool -> Prop,
    (forall proof, weak proof -> strong proof) /\
    (forall proof, ~ weak proof) /\ (exists proof, strong proof).
Proof.
  exists (fun _ => False), (fun _ => True); split; [| split].
  - intros _ H; contradiction.
  - intros _ H; contradiction.
  - exists false; exact I.
Qed.

(* Polynomials. *)

Record Poly : Type := mkPoly { pc : nat; pk : nat }.

Definition peval (p : Poly) (n : nat) : nat := pc p * (n + 1) ^ pk p.

Definition pcomp (q p : Poly) : Poly := mkPoly (pc q * (pc p + 1) ^ pk q) (pk p * pk q).

Theorem poly_mono : forall p m n, m <= n -> peval p m <= peval p n.
Proof.
  intros p m n H. unfold peval. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. lia.
Qed.

(* Composition lemma. *)
Theorem poly_comp_bound : forall q p n, peval q (peval p n) <= peval (pcomp q p) n.
Proof.
  intros q p n. unfold peval, pcomp; simpl.
  assert (Hx : 1 <= (n + 1) ^ pk p).
  { pose proof (Nat.pow_le_mono_l 1 (n + 1) (pk p) ltac:(lia)) as H.
    rewrite Nat.pow_1_l in H. exact H. }
  assert (H1 : pc p * (n + 1) ^ pk p + 1 <= (pc p + 1) * (n + 1) ^ pk p) by nia.
  assert (H2 : (pc p * (n + 1) ^ pk p + 1) ^ pk q <= ((pc p + 1) * (n + 1) ^ pk p) ^ pk q)
    by (apply Nat.pow_le_mono_l; exact H1).
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in H2.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. exact H2.
Qed.

(* Proof systems and p-simulation. *)

Record System (F : Type) : Type := mkSystem {
  Proof : Type;
  Proves : Proof -> F -> Prop;
  size : Proof -> nat
}.

Arguments mkSystem {F}.
Arguments Proof {F}.
Arguments Proves {F}.
Arguments size {F}.

Definition PSim {F : Type} (S1 S2 : System F) (q : Poly) : Prop :=
  forall (pi2 : Proof S2) (phi : F), Proves S2 pi2 phi ->
    exists pi1 : Proof S1, Proves S1 pi1 phi /\ size S1 pi1 <= peval q (size S2 pi2).

Definition LowerBound {F : Type} (S : System F) (phis : nat -> F) (L : nat -> nat) : Prop :=
  forall n (pi : Proof S), Proves S pi (phis n) -> L n <= size S pi.

Definition PolyBounded {F : Type} (S : System F) (taut : F -> Prop) (fsize : F -> nat)
    (p : Poly) : Prop :=
  forall phi, taut phi -> exists pi : Proof S, Proves S pi phi /\ size S pi <= peval p (fsize phi).

Definition SuperpolyLB {F : Type} (S : System F) (taut : F -> Prop) (fsize : F -> nat) : Prop :=
  forall p : Poly, exists phi, taut phi /\
    forall pi : Proof S, Proves S pi phi -> peval p (fsize phi) < size S pi.

Theorem superpoly_not_bounded {F : Type} (S : System F) (taut : F -> Prop) (fsize : F -> nat) :
  SuperpolyLB S taut fsize -> forall p, ~ PolyBounded S taut fsize p.
Proof.
  intros H p Hb. destruct (H p) as [phi [Hphi Hbig]].
  destruct (Hb phi Hphi) as [pi [Hpi Hs]].
  pose proof (Hbig pi Hpi). lia.
Qed.

(* Quantitative transfer. *)
Theorem lower_bound_transfer_quant {F : Type} (S1 S2 : System F) (q : Poly)
    (phis : nat -> F) (L : nat -> nat) :
  PSim S1 S2 q -> LowerBound S1 phis L ->
  forall n (pi2 : Proof S2), Proves S2 pi2 (phis n) -> L n <= peval q (size S2 pi2).
Proof.
  intros Hsim Hlb n pi2 H2.
  destruct (Hsim pi2 (phis n) H2) as [pi1 [H1 Hs]].
  pose proof (Hlb n pi1 H1). lia.
Qed.

(* Lower bounds transfer downward. *)
Theorem superpoly_transfer {F : Type} (S1 S2 : System F) (q : Poly) (taut : F -> Prop)
    (fsize : F -> nat) :
  PSim S1 S2 q -> SuperpolyLB S1 taut fsize -> SuperpolyLB S2 taut fsize.
Proof.
  intros Hsim Hlb p.
  destruct (Hlb (pcomp q p)) as [phi [Hphi Hbig]].
  exists phi. split; [exact Hphi|]. intros pi2 H2.
  destruct (Nat.lt_ge_cases (peval p (fsize phi)) (size S2 pi2)) as [Hlt | Hge];
    [exact Hlt|].
  exfalso.
  destruct (Hsim pi2 phi H2) as [pi1 [H1 Hs]].
  pose proof (Hbig pi1 H1).
  pose proof (poly_mono q _ _ Hge).
  pose proof (poly_comp_bound q p (fsize phi)).
  lia.
Qed.

(* Short proofs transfer upward. *)
Theorem poly_bounded_transfer {F : Type} (S1 S2 : System F) (q p : Poly) (taut : F -> Prop)
    (fsize : F -> nat) :
  PSim S1 S2 q -> PolyBounded S2 taut fsize p -> PolyBounded S1 taut fsize (pcomp q p).
Proof.
  intros Hsim Hb phi Hphi.
  destruct (Hb phi Hphi) as [pi2 [H2 Hs2]].
  destruct (Hsim pi2 phi H2) as [pi1 [H1 Hs1]].
  exists pi1. split; [exact H1|].
  pose proof (poly_mono q _ _ Hs2). pose proof (poly_comp_bound q p (fsize phi)). lia.
Qed.

Theorem psim_refl {F : Type} (S : System F) : PSim S S (mkPoly 1 1).
Proof. intros pi phi H. exists pi. split; [exact H|]. unfold peval; simpl. lia. Qed.

(* Transitivity. *)
Theorem psim_trans {F : Type} (S1 S2 S3 : System F) (q r : Poly) :
  PSim S1 S2 q -> PSim S2 S3 r -> PSim S1 S3 (pcomp q r).
Proof.
  intros H12 H23 pi3 phi H3.
  destruct (H23 pi3 phi H3) as [pi2 [H2 Hs2]].
  destruct (H12 pi2 phi H2) as [pi1 [H1 Hs1]].
  exists pi1. split; [exact H1|].
  pose proof (poly_mono q _ _ Hs2). pose proof (poly_comp_bound q r (size S3 pi3)). lia.
Qed.

(* Growth: c * (n + 1) ^ k < 2 ^ n eventually. *)

Lemma succ_le_two_pow : forall q, q + 1 <= 2 ^ q.
Proof. induction q as [|q IH]; simpl; lia. Qed.

Lemma lt_two_pow_self : forall a, a < 2 ^ a.
Proof. intros a. pose proof (succ_le_two_pow a). lia. Qed.

Theorem linear_lt_exp : forall a q, 2 * a + 1 <= q -> a * (q + 1) < 2 ^ q.
Proof.
  intros a q Hq.
  replace q with (2 * a + 1 + (q - (2 * a + 1))) by lia.
  generalize (q - (2 * a + 1)) as d. clear q Hq.
  induction d as [|d IH].
  - rewrite Nat.add_0_r.
    replace (2 * a + 1) with (a + S a) by lia.
    rewrite Nat.pow_add_r, Nat.pow_succ_r'.
    pose proof (succ_le_two_pow a). pose proof (lt_two_pow_self a).
    nia.
  - replace (2 * a + 1 + S d) with (S (2 * a + 1 + d)) by lia.
    rewrite Nat.pow_succ_r'.
    assert (a <= a * (2 * a + 1 + d + 1)) by nia.
    lia.
Qed.

Theorem dyadic_bracket : forall n, 1 <= n -> exists L, 2 ^ L <= n /\ n < 2 ^ (L + 1).
Proof.
  intros n Hn. replace n with (1 + (n - 1)) by lia.
  generalize (n - 1) as d. clear n Hn.
  induction d as [|d IH].
  - exists 0. simpl. lia.
  - destruct IH as [L [H1 H2]].
    destruct (Nat.lt_ge_cases (1 + S d) (2 ^ (L + 1))) as [H|H].
    + exists L. split; lia.
    + exists (L + 1). split; [lia|].
      replace (L + 1 + 1) with (S (L + 1)) by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

Theorem exp_beats_poly : forall c k n,
  2 ^ (2 * (c + k) + 1) <= n -> c * (n + 1) ^ k < 2 ^ n.
Proof.
  intros c d n Hn.
  assert (Hn1 : 1 <= n).
  { pose proof (Nat.pow_le_mono_r 2 0 (2 * (c + d) + 1) ltac:(lia) ltac:(lia)).
    rewrite Nat.pow_0_r in H. lia. }
  destruct (dyadic_bracket n Hn1) as [L [HL1 HL2]].
  assert (HLbig : 2 * (c + d) + 1 <= L).
  { destruct (Nat.le_gt_cases (2 * (c + d) + 1) L) as [H|H]; auto.
    pose proof (Nat.pow_le_mono_r 2 (L + 1) (2 * (c + d) + 1) ltac:(lia) ltac:(lia)).
    lia. }
  pose proof (linear_lt_exp (c + d) L HLbig) as Hlin.
  assert (Hsum : c + d * (L + 1) < n).
  { assert (c <= c * (L + 1)) by nia.
    rewrite Nat.mul_add_distr_r in Hlin. lia. }
  assert (Hbase : (n + 1) ^ d <= 2 ^ ((L + 1) * d)).
  { rewrite Nat.pow_mul_r. apply Nat.pow_le_mono_l. lia. }
  pose proof (lt_two_pow_self c) as Hc.
  assert (Hpos : 0 < 2 ^ ((L + 1) * d)).
  { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
  apply Nat.le_lt_trans with (c * 2 ^ ((L + 1) * d)).
  { apply Nat.mul_le_mono_l. exact Hbase. }
  apply Nat.lt_le_trans with (2 ^ c * 2 ^ ((L + 1) * d)).
  { apply Nat.mul_lt_mono_pos_r; auto. }
  rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
Qed.

(* General countermodel: weak lower bounds, strong short proofs. *)

Definition weakSys {F : Type} (taut : F -> Prop) (fsize : F -> nat) : System F :=
  mkSystem F (fun pi phi => pi = phi /\ taut phi) (fun pi => 2 ^ fsize pi).

Definition strongSys {F : Type} (taut : F -> Prop) (fsize : F -> nat) : System F :=
  mkSystem F (fun pi phi => pi = phi /\ taut phi) fsize.

Theorem sys_sound_complete {F : Type} (taut : F -> Prop) (fsize : F -> nat) (phi : F) :
  (taut phi <-> exists pi : Proof (weakSys taut fsize), Proves (weakSys taut fsize) pi phi) /\
  (taut phi <-> exists pi : Proof (strongSys taut fsize), Proves (strongSys taut fsize) pi phi).
Proof.
  split; split.
  - intro H. exists phi. simpl. split; [reflexivity | exact H].
  - intros [pi [_ H]]. exact H.
  - intro H. exists phi. simpl. split; [reflexivity | exact H].
  - intros [pi [_ H]]. exact H.
Qed.

(* General countermodel. *)
Theorem weak_lb_strong_short {F : Type} (taut : F -> Prop) (fsize : F -> nat) :
  (forall m, exists phi, taut phi /\ m <= fsize phi) ->
  SuperpolyLB (weakSys taut fsize) taut fsize /\
  PolyBounded (strongSys taut fsize) taut fsize (mkPoly 1 1) /\
  ~ SuperpolyLB (strongSys taut fsize) taut fsize /\
  PSim (strongSys taut fsize) (weakSys taut fsize) (mkPoly 1 1).
Proof.
  intros Hunb.
  assert (Hb : PolyBounded (strongSys taut fsize) taut fsize (mkPoly 1 1)).
  { intros phi Hphi. exists phi. simpl. split; [split; [reflexivity | exact Hphi]|].
    unfold peval; simpl. lia. }
  split; [| split; [exact Hb | split]].
  - intros p. destruct (Hunb (2 ^ (2 * (pc p + pk p) + 1))) as [phi [Hphi Hm]].
    exists phi. split; [exact Hphi|]. simpl. intros pi [E _]. subst pi.
    unfold peval. apply exp_beats_poly. exact Hm.
  - intro H. apply (superpoly_not_bounded _ taut fsize H (mkPoly 1 1)). exact Hb.
  - intros pi phi [E Hphi]. subst pi. exists phi. simpl.
    split; [split; [reflexivity | exact Hphi]|].
    unfold peval; simpl. pose proof (lt_two_pow_self (fsize phi)). lia.
Qed.

(* The obligation. *)

Definition SuperpolyAllSystems {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) : Prop :=
  forall S, C S -> SuperpolyLB S taut fsize.

(* Optimal systems reduce the obligation to one lower bound. *)
Theorem optimal_system_reduces {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) (S : System F) :
  C S -> (forall T, C T -> exists q, PSim S T q) ->
  (SuperpolyAllSystems C taut fsize <-> SuperpolyLB S taut fsize).
Proof.
  intros HS Hopt. split.
  - intro H. apply H. exact HS.
  - intros H T HT. destruct (Hopt T HT) as [q Hq].
    apply (superpoly_transfer S T q taut fsize Hq H).
Qed.

Theorem bounded_member_refutes {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) (S : System F) (p : Poly) :
  C S -> PolyBounded S taut fsize p -> ~ SuperpolyAllSystems C taut fsize.
Proof.
  intros HS Hb H. apply (superpoly_not_bounded S taut fsize (H S HS) p). exact Hb.
Qed.

Example comp_check : peval (mkPoly 2 1) (peval (mkPoly 1 2) 2) <= peval (pcomp (mkPoly 2 1) (mkPoly 1 2)) 2.
Proof. apply Nat.leb_le. reflexivity. Qed.
