(* Issue #532, Idea 39: proof-system scope (lower bounds and p-simulation).

   Rocq twin of ../lean/Idea39.lean (same theorem names and content, except
   as listed below). Abstract Cook-Reckhow setting: a proof system over
   formulas F is a relation Proves : Proof -> F -> Prop with
   size : Proof -> nat; polynomials are pairs (c, k) evaluated as
   c * (n + 1) ^ k. Lower bounds transfer downward along p-simulation
   (superpoly_transfer), short proofs transfer upward (poly_bounded_transfer),
   p-simulation is a preorder (psim_refl, psim_trans), and a general
   countermodel (weak_lb_strong_short) shows that a lower bound for a weak
   system is consistent with short proofs in a stronger one. The abstract
   schema is SuperpolyAllSystemsFor.

   Machine part: Cook-Reckhow systems (CRSystem) over the shared machine
   model, the open obligation AllTautSystemsSuperpolynomial for
   TAUT = complement SAT, the proved links to NP (inNP_of_crPolyBounded,
   crPolyBounded_of_inP), the conditional theorems towards P <> NP and
   NP <> coNP (SATInNP is proved in SATVerifier.v as SATVerifier.satInNP,
   so pNotEqualsNP_of_allTautSystemsSuperpolynomial' and
   npNeCoNP_of_not_inNP_taut' drop that premise), the known theorem as a named premise CookReckhow, and
   non-vacuity of the schema AllCRSystemsSuperpolynomialFor
   (crSchema_nontrivial).

   Differences from Lean:
   - superpolyLB_iff_forall_not_polyBounded, allCRSystemsSuperpolynomial_iff,
     allCRSystemsSuperpolynomial_of_not_inNP and
     allTautSystemsSuperpolynomial_of_not_inNP take excluded middle as an
     explicit premise (forall P : Prop, P \/ ~ P). The directions that need
     no premise are superpoly_not_bounded and
     allCRSystemsSuperpolynomial_not_polyBounded.
   - verifierLanguage is a predicate (Word -> Prop) rather than a
     classically decided Language, and verifierLanguage_eq states
     L x = true <-> verifierLanguage (verifier P) x pointwise.
   - exists_allSuperpolynomial is proved by a direct pointwise diagonal
     (crDiag) over codes of (verifier, polynomial) pairs instead of Cantor
     over verifierLanguage: on the code x of (v, Q), crDiag rejects exactly
     when v accepts x with some proof of length at most Q(|x|) within a clock
     of Q(|x| + Q(|x|) + 1) steps. Every Cook-Reckhow system for crDiag is
     therefore superpolynomial (the statement is the same as in Lean).
   See ../ideas/Idea39.md. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue532.rocq Require SATVerifier.

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

(** Schema over a class C of systems: every system in C has a
    superpolynomial lower bound. The class is a free argument; the machine
    instance for Cook-Reckhow systems for TAUT is AllTautSystemsSuperpolynomial
    below. *)
Definition SuperpolyAllSystemsFor {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) : Prop :=
  forall S, C S -> SuperpolyLB S taut fsize.

(* Optimal systems reduce the obligation to one lower bound. *)
Theorem optimal_system_reduces {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) (S : System F) :
  C S -> (forall T, C T -> exists q, PSim S T q) ->
  (SuperpolyAllSystemsFor C taut fsize <-> SuperpolyLB S taut fsize).
Proof.
  intros HS Hopt. split.
  - intro H. apply H. exact HS.
  - intros H T HT. destruct (Hopt T HT) as [q Hq].
    apply (superpoly_transfer S T q taut fsize Hq H).
Qed.

Theorem bounded_member_refutes {F : Type} (C : System F -> Prop) (taut : F -> Prop)
    (fsize : F -> nat) (S : System F) (p : Poly) :
  C S -> PolyBounded S taut fsize p -> ~ SuperpolyAllSystemsFor C taut fsize.
Proof.
  intros HS Hb H. apply (superpoly_not_bounded S taut fsize (H S HS) p). exact Hb.
Qed.

Example comp_check : peval (mkPoly 2 1) (peval (mkPoly 1 2) 2) <= peval (pcomp (mkPoly 2 1) (mkPoly 1 2)) 2.
Proof. apply Nat.leb_le. reflexivity. Qed.


(* ---------- Machine part: Cook-Reckhow systems for TAUT ---------- *)

(** TAUT in the shared encoding: the complement of SAT. A CNF word is in TAUT
    exactly when its formula has no satisfying assignment. *)
Definition TAUT : Language := complement SAT.

(** A Cook-Reckhow proof system for L in the shared machine model: a verifier
    program that halts within the polynomial timeBound on every
    (input, proof) pair, accepts only members of L, and accepts every member
    with some proof. *)
Record CRSystem (L : Language) : Type := mkCRSystem {
  verifier : VerifierProgram;
  timeBound : Polynomial;
  halts : forall x pi, exists t b,
    t <= timeLimit verifier timeBound x pi /\ verifierRun verifier x pi t b;
  sound : forall x pi t, verifierRun verifier x pi t true -> L x = true;
  complete : forall x, L x = true -> exists pi t, verifierRun verifier x pi t true
}.

Arguments verifier {L}.
Arguments timeBound {L}.
Arguments halts {L}.
Arguments sound {L}.
Arguments complete {L}.

(** The abstract system over words carried by a Cook-Reckhow system: proofs
    are words, a proof proves x when the verifier accepts (x, pi), and the
    size of a proof is its length. *)
Definition toSystem {L : Language} (P : CRSystem L) : System Word :=
  mkSystem Word (fun pi x => exists t, verifierRun (verifier P) x pi t true)
    (@length bool).

(** The class of abstract systems coming from Cook-Reckhow systems for L. *)
Definition CRClass (L : Language) : System Word -> Prop :=
  fun S => exists P : CRSystem L, toSystem P = S.

(** The membership predicate of a language. *)
Definition memberOf (L : Language) : Word -> Prop := fun x => L x = true.

(** Polynomial boundedness of a Cook-Reckhow system. *)
Definition CRPolyBounded {L : Language} (P : CRSystem L) : Prop :=
  exists p : Poly, PolyBounded (toSystem P) (memberOf L) (@length bool) p.

(* A superpolynomial lower bound is exactly the failure of every polynomial
   bound (given excluded middle; the forward direction is
   superpoly_not_bounded). *)
Theorem superpolyLB_iff_forall_not_polyBounded : (forall P : Prop, P \/ ~ P) ->
  forall {F : Type} (S : System F) (taut : F -> Prop) (fsize : F -> nat),
  SuperpolyLB S taut fsize <-> forall p, ~ PolyBounded S taut fsize p.
Proof.
  intros classic F S taut fsize; split; [apply superpoly_not_bounded|].
  intros h p.
  destruct (classic (exists phi, taut phi /\
    forall pi : Proof S, Proves S pi phi -> peval p (fsize phi) < size S pi))
    as [Hyes | hne]; [exact Hyes|].
  exfalso; apply (h p); intros phi hphi.
  destruct (classic (exists pi : Proof S, Proves S pi phi /\
    size S pi <= peval p (fsize phi))) as [Hpi | hno]; [exact Hpi|].
  exfalso; apply hne; exists phi; split; [exact hphi|].
  intros pi hpi.
  destruct (Nat.lt_ge_cases (peval p (fsize phi)) (size S pi)) as [Hlt | Hge];
    [exact Hlt|].
  exfalso; apply hno; exists pi; split; assumption.
Qed.

(** Schema over languages: every Cook-Reckhow system for L has a
    superpolynomial lower bound. The language is a free argument; the
    obligation is the instance AllTautSystemsSuperpolynomial. *)
Definition AllCRSystemsSuperpolynomialFor (L : Language) : Prop :=
  forall P : CRSystem L, SuperpolyLB (toSystem P) (memberOf L) (@length bool).

(** Open obligation (Cook's program). Every Cook-Reckhow proof system for
    TAUT = complement SAT (a polynomial-time machine verifier, sound and
    complete) has a superpolynomial lower bound: for every polynomial p some
    member x of TAUT has only accepted proofs longer than p |x|. With the
    named known theorem CookReckhow this is equivalent to NP <> coNP. *)
Definition AllTautSystemsSuperpolynomial : Prop :=
  forall P : CRSystem (complement SAT),
    SuperpolyLB (toSystem P) (fun x => complement SAT x = true) (@length bool).

Theorem allTautSystemsSuperpolynomial_iff_for :
  AllTautSystemsSuperpolynomial <-> AllCRSystemsSuperpolynomialFor TAUT.
Proof. split; intros H; exact H. Qed.

(* The obligation is the abstract schema for the class of Cook-Reckhow
   systems for TAUT. *)
Theorem allTautSystemsSuperpolynomial_iff_class :
  AllTautSystemsSuperpolynomial <->
    SuperpolyAllSystemsFor (CRClass TAUT) (memberOf TAUT) (@length bool).
Proof.
  split.
  - intros h S [P <-]; exact (h P).
  - intros h P; exact (h (toSystem P) (ex_intro _ P eq_refl)).
Qed.

(* Constructive direction of allCRSystemsSuperpolynomial_iff. *)
Theorem allCRSystemsSuperpolynomial_not_polyBounded : forall L : Language,
  AllCRSystemsSuperpolynomialFor L -> forall P : CRSystem L, ~ CRPolyBounded P.
Proof.
  intros L h P [p hp]; exact (superpoly_not_bounded _ _ _ (h P) p hp).
Qed.

(* The schema for L is the absence of a polynomially bounded system. *)
Theorem allCRSystemsSuperpolynomial_iff : (forall P : Prop, P \/ ~ P) ->
  forall L : Language,
  AllCRSystemsSuperpolynomialFor L <-> forall P : CRSystem L, ~ CRPolyBounded P.
Proof.
  intros classic L; split; [apply allCRSystemsSuperpolynomial_not_polyBounded|].
  intros h P.
  apply (proj2 (superpolyLB_iff_forall_not_polyBounded classic _ _ _)).
  intros p hp; exact (h P (ex_intro _ p hp)).
Qed.

(* Optimal systems reduce the obligation to one machine lower bound. *)
Theorem optimal_crSystem_reduces : forall P : CRSystem TAUT,
  (forall Q : CRSystem TAUT, exists q, PSim (toSystem P) (toSystem Q) q) ->
  (AllTautSystemsSuperpolynomial <->
     SuperpolyLB (toSystem P) (memberOf TAUT) (@length bool)).
Proof.
  intros P hopt.
  eapply iff_trans; [apply allTautSystemsSuperpolynomial_iff_class|].
  apply optimal_system_reduces.
  - exists P; reflexivity.
  - intros T [Q <-]; exact (hopt Q).
Qed.

(* Verifier runs are deterministic. *)
Theorem verifierRun_deterministic : forall v x pi t t' b b',
  verifierRun v x pi t b -> verifierRun v x pi t' b' -> t = t' /\ b = b'.
Proof.
  intros [m | m] x pi t t' b b' h h'; simpl in h, h'; exact (run_deterministic _ _ _ _ _ _ h h').
Qed.

(* A polynomially bounded Cook-Reckhow system puts L in NP. *)
Theorem inNP_of_crPolyBounded : forall {L : Language} (P : CRSystem L),
  CRPolyBounded P -> InNP L.
Proof.
  intros L P [q hq].
  assert (hc : forall x, L x = true <->
    exists cert t, length cert <= evalPoly {| coefficient := pc q; degree := pk q |} (length x) /\
      t <= timeLimit (verifier P) (timeBound P) x cert /\
      verifierRun (verifier P) x cert t true).
  { intros x; split.
    - intros hx; destruct (hq x hx) as [pi [[t hr] hlen]].
      destruct (halts P x pi) as [t' [b' [ht' hr']]].
      destruct (verifierRun_deterministic _ _ _ _ _ _ _ hr hr') as [<- _].
      exists pi, t; split; [exact hlen|]; split; [exact ht' | exact hr].
    - intros [pi [t [_ [_ hr]]]]; exact (sound P x pi t hr). }
  exists (Build_ClassNP L (verifier P) (timeBound P)
    {| coefficient := pc q; degree := pk q |} (fun x cert _ => halts P x cert) hc).
  reflexivity.
Qed.

(* Every language in P has a polynomially bounded Cook-Reckhow system: the
   decider ignores the proof, and the empty proof suffices. *)
Theorem crPolyBounded_of_inP : forall {L : Language}, InP L ->
  exists P : CRSystem L, CRPolyBounded P.
Proof.
  intros L h; apply polyDec_iff_inP in h; destruct h as [m [p hm]].
  assert (hh : forall x pi, exists t b,
    t <= timeLimit (ignoreCertificate m) p x pi /\ verifierRun (ignoreCertificate m) x pi t b).
  { intros x pi; destruct (hm x) as [t [b [ht [hr _]]]]; exists t, b; split; assumption. }
  assert (hs : forall x pi t, verifierRun (ignoreCertificate m) x pi t true -> L x = true).
  { intros x pi t hr; simpl in hr; destruct (hm x) as [t' [b' [_ [hr' hb']]]].
    destruct (run_deterministic _ _ _ _ _ _ hr hr') as [_ <-]; symmetry; exact hb'. }
  assert (hcpl : forall x, L x = true ->
    exists pi t, verifierRun (ignoreCertificate m) x pi t true).
  { intros x hx; destruct (hm x) as [t [b [_ [hr hb]]]].
    rewrite hx in hb; subst b; exists [], t; exact hr. }
  exists (mkCRSystem L (ignoreCertificate m) p hh hs hcpl).
  exists (mkPoly 0 0); intros x hx.
  destruct (hm x) as [t [b [_ [hr hb]]]].
  unfold memberOf in hx; rewrite hx in hb; subst b.
  exists []; simpl; split; [exists t; exact hr | lia].
Qed.

(* A language outside NP satisfies the schema (given excluded middle). *)
Theorem allCRSystemsSuperpolynomial_of_not_inNP : (forall P : Prop, P \/ ~ P) ->
  forall {L : Language}, ~ InNP L -> AllCRSystemsSuperpolynomialFor L.
Proof.
  intros classic L h.
  apply (proj2 (allCRSystemsSuperpolynomial_iff classic L)).
  intros P hP; exact (h (inNP_of_crPolyBounded P hP)).
Qed.

(* A language in P violates the schema. *)
Theorem not_allCRSystemsSuperpolynomial_of_inP : forall {L : Language},
  InP L -> ~ AllCRSystemsSuperpolynomialFor L.
Proof.
  intros L h hall; destruct (crPolyBounded_of_inP h) as [P hP].
  exact (allCRSystemsSuperpolynomial_not_polyBounded L hall P hP).
Qed.

(* TAUT outside NP gives the obligation (given excluded middle). *)
Theorem allTautSystemsSuperpolynomial_of_not_inNP : (forall P : Prop, P \/ ~ P) ->
  ~ InNP TAUT -> AllTautSystemsSuperpolynomial.
Proof. intros classic h; exact (allCRSystemsSuperpolynomial_of_not_inNP classic h). Qed.

(* The obligation gives SAT outside P unconditionally. *)
Theorem not_inP_sat_of_allTautSystemsSuperpolynomial :
  AllTautSystemsSuperpolynomial -> ~ InP SAT.
Proof.
  intros h hs; exact (not_allCRSystemsSuperpolynomial_of_inP (inP_complement _ hs) h).
Qed.

(* Conditional theorem: with SAT in NP (a named Cook-Levin half), the
   obligation gives P <> NP. *)
Theorem pNotEqualsNP_of_allTautSystemsSuperpolynomial :
  SATInNP -> AllTautSystemsSuperpolynomial -> PNotEqualsNP.
Proof.
  intros mem h hp.
  exact (not_inP_sat_of_allTautSystemsSuperpolynomial h (inP_sat_of_pEqualsNP mem hp)).
Qed.

(** [SATInNP] is proved ([SATVerifier.satInNP]), so the premise is dropped. *)
Theorem pNotEqualsNP_of_allTautSystemsSuperpolynomial' :
  AllTautSystemsSuperpolynomial -> PNotEqualsNP.
Proof. exact (pNotEqualsNP_of_allTautSystemsSuperpolynomial SATVerifier.satInNP). Qed.

(* TAUT outside NP gives NP <> coNP, given SAT in NP. *)
Theorem npNeCoNP_of_not_inNP_taut : SATInNP -> ~ InNP TAUT -> ~ NPEqualsCoNP.
Proof. intros mem h heq; exact (h (proj1 (heq SAT) mem)). Qed.

(** [SATInNP] is proved ([SATVerifier.satInNP]), so the premise is dropped. *)
Theorem npNeCoNP_of_not_inNP_taut' : ~ InNP TAUT -> ~ NPEqualsCoNP.
Proof. exact (npNeCoNP_of_not_inNP_taut SATVerifier.satInNP). Qed.

(** Known theorem, not mechanised here: every Cook-Reckhow system for TAUT is
    superpolynomial iff NP <> coNP (S. A. Cook and R. A. Reckhow, "The
    relative efficiency of propositional proof systems", J. Symbolic Logic
    44(1), 1979, Theorem 1.5). *)
Definition CookReckhow : Prop := AllTautSystemsSuperpolynomial <-> ~ NPEqualsCoNP.

(* Conditional theorem (named premise): the obligation gives NP <> coNP. *)
Theorem npNeCoNP_of_allTautSystemsSuperpolynomial : CookReckhow ->
  AllTautSystemsSuperpolynomial -> ~ NPEqualsCoNP.
Proof. intros hCR h; exact (proj1 hCR h). Qed.

(* Conditional theorem (named premise): the obligation gives P <> NP through
   NP <> coNP. *)
Theorem pNotEqualsNP_via_cookReckhow : CookReckhow ->
  AllTautSystemsSuperpolynomial -> PNotEqualsNP.
Proof.
  intros hCR h; exact (pNotEqualsNP_of_npNeCoNP
    (npNeCoNP_of_allTautSystemsSuperpolynomial hCR h)).
Qed.

(* With CookReckhow, NP <> coNP gives the obligation. *)
Theorem allTautSystemsSuperpolynomial_of_npNeCoNP : CookReckhow ->
  ~ NPEqualsCoNP -> AllTautSystemsSuperpolynomial.
Proof. intros hCR h; exact (proj2 hCR h). Qed.

(* ---------- Non-vacuity ---------- *)

Definition emptyMachine : Machine := {| program := [] |}.

(* The machine with no instructions halts with false after one step. *)
Theorem emptyMachine_run : forall x, Run emptyMachine (initial x) 1 false.
Proof. intro x. apply run_halt. destruct x; reflexivity. Qed.

Theorem inP_const_false : InP (fun _ => false).
Proof.
  apply (inP_of_decidesWithin emptyMachine {| coefficient := 1; degree := 0 |}).
  intro x. exists 1, false. split; [unfold evalPoly; simpl; lia |].
  split; [apply emptyMachine_run | reflexivity].
Qed.

(* Non-vacuity, false side: the schema fails for the constant-false
   language. *)
Theorem const_false_not_allSuperpolynomial :
  ~ AllCRSystemsSuperpolynomialFor (fun _ => false).
Proof. exact (not_allCRSystemsSuperpolynomial_of_inP inP_const_false). Qed.

(** Injective encoding of verifier programs. *)
Definition encVerifier (v : VerifierProgram) : Word :=
  match v with
  | ignoreCertificate m => false :: encMachine m
  | paired m => true :: encMachine m
  end.

Theorem encVerifier_injective : forall v w, encVerifier v = encVerifier w -> v = w.
Proof.
  intros [m | m] [m' | m'] h; simpl in h; injection h; intros; try discriminate;
    f_equal; apply encMachine_injective; assumption.
Qed.

(** The inputs with some accepted proof (a predicate; Lean decides it
    classically). *)
Definition verifierLanguage (v : VerifierProgram) (x : Word) : Prop :=
  exists pi t, verifierRun v x pi t true.

Theorem verifierLanguage_eq : forall {L : Language} (P : CRSystem L) x,
  L x = true <-> verifierLanguage (verifier P) x.
Proof.
  intros L P x; split.
  - apply complete.
  - intros [pi [t hr]]; exact (sound P x pi t hr).
Qed.

(* The pointwise diagonal. *)

Definition verifierMachine (v : VerifierProgram) : Machine :=
  match v with ignoreCertificate m => m | paired m => m end.

Definition verifierConfig (v : VerifierProgram) (x pi : Word) : Config :=
  match v with ignoreCertificate _ => initial x | paired _ => pairedInput x pi end.

Lemma verifierRun_iff : forall v x pi t b,
  verifierRun v x pi t b <-> Run (verifierMachine v) (verifierConfig v x pi) t b.
Proof. intros [m | m] x pi t b; simpl; split; intros h; exact h. Qed.

(** Code of a (verifier, polynomial) pair. *)
Definition encVerifierPoly (v : VerifierProgram) (Q : Polynomial) : Word :=
  match v with
  | ignoreCertificate m => false :: encMachinePoly (m, Q)
  | paired m => true :: encMachinePoly (m, Q)
  end.

Definition decVerifierPoly (w : Word) : option (VerifierProgram * Polynomial) :=
  match w with
  | [] => None
  | b :: r =>
      match decMachinePoly r with
      | Some (m, Q) => Some (if b then paired m else ignoreCertificate m, Q)
      | None => None
      end
  end.

Lemma decVerifierPoly_encVerifierPoly : forall v Q,
  decVerifierPoly (encVerifierPoly v Q) = Some (v, Q).
Proof. intros [m | m] Q; simpl; rewrite decMachinePoly_encMachinePoly; reflexivity. Qed.

(** All words of length at most n. *)
Definition wordsUpTo (n : nat) : list Word := flat_map allAssignments (seq 0 (S n)).

Lemma in_wordsUpTo : forall n (w : Word), length w <= n -> In w (wordsUpTo n).
Proof.
  intros n w h; unfold wordsUpTo; apply in_flat_map; exists (length w); split.
  - apply in_seq; lia.
  - apply mem_allAssignments_iff; reflexivity.
Qed.

(** Does v accept (x, pi) within fuel steps? *)
Definition acceptsWithin (v : VerifierProgram) (x pi : Word) (fuel : nat) : bool :=
  match runFor (verifierMachine v) (verifierConfig v x pi) fuel with
  | Some true => true
  | _ => false
  end.

(** The diagonal language: on the code of (v, Q) it rejects exactly when v
    accepts some proof of length at most Q(|w|) within Q(|w| + Q(|w|) + 1)
    steps. *)
Definition crDiag : Language := fun w =>
  match decVerifierPoly w with
  | Some (v, Q) =>
      negb (existsb (fun pi => acceptsWithin v w pi
                                 (evalPoly Q (length w + evalPoly Q (length w) + 1)))
              (wordsUpTo (evalPoly Q (length w))))
  | None => true
  end.

Lemma evalPoly_le : forall (P Q : Polynomial) a b,
  coefficient P <= coefficient Q -> degree P <= degree Q -> a <= b ->
  evalPoly P a <= evalPoly Q b.
Proof.
  intros P Q a b hc hd hab; unfold evalPoly.
  apply Nat.mul_le_mono; [exact hc|].
  apply Nat.le_trans with ((b + 1) ^ degree P).
  - apply Nat.pow_le_mono_l; lia.
  - apply Nat.pow_le_mono_r; lia.
Qed.

Lemma timeLimit_le : forall v (Q : Polynomial) x pi,
  timeLimit v Q x pi <= evalPoly Q (length x + length pi + 1).
Proof.
  intros [m | m] Q x pi; simpl; [| lia].
  apply evalPoly_le; lia.
Qed.

(* Every Cook-Reckhow system for crDiag is superpolynomial. *)
Theorem crDiag_allSuperpolynomial : AllCRSystemsSuperpolynomialFor crDiag.
Proof.
  intros P p.
  set (v := verifier P).
  set (Q := {| coefficient := pc p + coefficient (timeBound P);
               degree := pk p + degree (timeBound P) |}).
  set (x := encVerifierPoly v Q).
  set (fuel := evalPoly Q (length x + evalPoly Q (length x) + 1)).
  assert (hdiag : crDiag x = negb (existsb (fun pi => acceptsWithin v x pi fuel)
                                     (wordsUpTo (evalPoly Q (length x))))).
  { unfold crDiag at 1; unfold x at 1; rewrite decVerifierPoly_encVerifierPoly.
    reflexivity. }
  assert (hacc : forall pi, acceptsWithin v x pi fuel = true -> crDiag x = true).
  { intros pi ha; unfold acceptsWithin in ha.
    destruct (runFor (verifierMachine v) (verifierConfig v x pi) fuel) as [[|]|] eqn:hr;
      try discriminate.
    destruct (run_of_runFor _ _ _ _ hr) as [t [_ ht]].
    apply (sound P x pi t), verifierRun_iff; exact ht. }
  assert (hx : crDiag x = true).
  { destruct (existsb (fun pi => acceptsWithin v x pi fuel)
                (wordsUpTo (evalPoly Q (length x)))) eqn:he.
    - apply existsb_exists in he; destruct he as [pi [_ ha]]; exact (hacc pi ha).
    - rewrite hdiag; reflexivity. }
  exists x; split; [exact hx|].
  intros pi [t hr]; simpl.
  destruct (Nat.lt_ge_cases (peval p (length x)) (length pi)) as [Hlt | Hge];
    [exact Hlt|].
  exfalso.
  assert (hq : length pi <= evalPoly Q (length x)).
  { apply Nat.le_trans with (peval p (length x)); [exact Hge|].
    unfold peval, evalPoly, Q; simpl.
    apply Nat.mul_le_mono; [lia|]; apply Nat.pow_le_mono_r; lia. }
  destruct (halts P x pi) as [t' [b' [ht' hr']]].
  destruct (verifierRun_deterministic _ _ _ _ _ _ _ hr hr') as [<- _].
  assert (hfuel : t <= fuel).
  { apply Nat.le_trans with (timeLimit v (timeBound P) x pi); [exact ht'|].
    apply Nat.le_trans with (evalPoly (timeBound P) (length x + length pi + 1));
      [apply timeLimit_le|].
    unfold fuel; apply evalPoly_le; simpl; lia. }
  assert (ha : acceptsWithin v x pi fuel = true).
  { assert (E : runFor (verifierMachine v) (verifierConfig v x pi) fuel = Some true)
      by exact (runFor_of_run _ _ _ _ (proj1 (verifierRun_iff _ _ _ _ _) hr) fuel hfuel).
    unfold acceptsWithin; rewrite E; reflexivity. }
  assert (he : existsb (fun pi => acceptsWithin v x pi fuel)
                 (wordsUpTo (evalPoly Q (length x))) = true).
  { apply existsb_exists; exists pi; split; [apply in_wordsUpTo; exact hq | exact ha]. }
  rewrite hdiag, he in hx; discriminate.
Qed.

(* Non-vacuity, true side: some language satisfies the schema. *)
Theorem exists_allSuperpolynomial : exists L : Language, AllCRSystemsSuperpolynomialFor L.
Proof. exists crDiag; exact crDiag_allSuperpolynomial. Qed.

(* The schema is satisfiable and refutable. *)
Theorem crSchema_nontrivial :
  (exists L, AllCRSystemsSuperpolynomialFor L) /\
  (exists L, ~ AllCRSystemsSuperpolynomialFor L).
Proof.
  split; [exact exists_allSuperpolynomial|].
  exists (fun _ => false); exact const_false_not_allSuperpolynomial.
Qed.
