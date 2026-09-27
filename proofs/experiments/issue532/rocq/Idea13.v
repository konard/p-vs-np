(* Issue #532, Idea 13: from approximation to exactness.

   Rocq counterpart of lean/Idea13.lean; theorem names are aligned.

   Ratios are written multiplicatively in nat.  Proved in general:
   a (1 + 1/q)-approximation of an integer minimum OPT with OPT < q is exact
   (approx_exact_nat), and similarly for maximisation (approx_exact_max);
   the bound is sharp (threshold_sharp); a 2-approximation need not be exact
   (ratio_two_not_exact); an approximation scheme run with q = B x > OPT x is
   exact (scheme_exact_below_bound) and polynomial when the scheme is fully
   polynomial and B is polynomially bounded (fptas_poly_bounded_exact); and an
   approximation algorithm decides every gap promise problem with a larger gap
   (approx_decides_gap, polyApprox_decides_gap).

   Verdict: approximation gives exactness only below an integrality gap; the
   open obligation PolyApprox beyond a published NP-hardness threshold would
   itself prove P = NP.  Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool.

(** Minimisation: OPT <= A, A*q <= OPT*(q+1), OPT < q  imply  A = OPT. *)
Theorem approx_exact_nat : forall A OPT q,
  OPT <= A -> A * q <= OPT * (q + 1) -> OPT < q -> A = OPT.
Proof. intros A OPT q h1 h2 h3. nia. Qed.

(** Maximisation: A <= OPT, OPT*q <= A*(q+1), OPT <= q  imply  A = OPT. *)
Theorem approx_exact_max : forall A OPT q,
  A <= OPT -> OPT * q <= A * (q + 1) -> OPT <= q -> A = OPT.
Proof. intros A OPT q h1 h2 h3. nia. Qed.

(** The bound OPT < q is sharp: with OPT = q, the value q + 1 is
    (1+1/q)-approximate but not optimal. *)
Theorem threshold_sharp : forall q,
  q <= q + 1 /\ (q + 1) * q <= q * (q + 1) /\ q + 1 <> q.
Proof. intro q. split; [lia|]. split; [rewrite Nat.mul_comm; lia | lia]. Qed.

(** For every OPT >= 1, 2*OPT is a 2-approximation that is not optimal. *)
Theorem ratio_two_not_exact : forall OPT, 1 <= OPT ->
  exists A, OPT <= A /\ A <= 2 * OPT /\ A <> OPT.
Proof. intros OPT h. exists (2 * OPT). lia. Qed.

(** An approximation scheme run with q = B x > OPT x is exact. *)
Theorem scheme_exact_below_bound : forall {T : Type} (opt : T -> nat)
  (S : nat -> T -> nat) (B : T -> nat),
  (forall q x, opt x <= S q x /\ S q x * q <= opt x * (q + 1)) ->
  (forall x, opt x < B x) -> forall x, S (B x) x = opt x.
Proof.
  intros T opt S B hS hB x. destruct (hS (B x) x) as [h1 h2].
  exact (approx_exact_nat _ _ _ h1 h2 (hB x)).
Qed.

(** Fully polynomial scheme + polynomially bounded optimum
    => polynomial exact algorithm, with explicit constants. *)
Theorem fptas_poly_bounded_exact : forall {T : Type} (sz opt : T -> nat)
  (S Tm : nat -> T -> nat) (B : T -> nat) (c d e k : nat),
  (forall q x, opt x <= S q x /\ S q x * q <= opt x * (q + 1)) ->
  (forall q x, Tm q x <= c * (sz x + q + 1) ^ d) ->
  (forall x, opt x < B x) -> (forall x, B x <= e * (sz x + 1) ^ k) ->
  forall x, S (B x) x = opt x /\
    Tm (B x) x <= c * (e + 1) ^ d * (sz x + 1) ^ ((k + 1) * d).
Proof.
  intros T sz opt S Tm B c d e k hS hT hB hBp x. split.
  - exact (scheme_exact_below_bound opt S B hS hB x).
  - pose proof (Nat.pow_le_mono_r (sz x + 1) 1 (k + 1) ltac:(lia) ltac:(lia)) as p1.
    rewrite Nat.pow_1_r in p1.
    pose proof (Nat.pow_le_mono_r (sz x + 1) k (k + 1) ltac:(lia) ltac:(lia)) as p2.
    pose proof (Nat.mul_le_mono_l _ _ e p2) as p3.
    pose proof (hBp x) as hb.
    assert (hbase : sz x + B x + 1 <= (e + 1) * (sz x + 1) ^ (k + 1)) by lia.
    pose proof (Nat.pow_le_mono_l _ _ d hbase) as hpow.
    rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in hpow.
    rewrite <- Nat.mul_assoc.
    eapply Nat.le_trans; [apply hT|]. apply Nat.mul_le_mono_l. exact hpow.
Qed.

(** Gap decision: under the promise opt x <= a \/ a*num < opt x * den, an
    algorithm with ratio num/den decides which case holds. *)
Theorem approx_decides_gap : forall {T : Type} (opt A : T -> nat) (a num den : nat),
  (forall x, opt x <= A x /\ A x * den <= opt x * num) ->
  (forall x, opt x <= a \/ a * num < opt x * den) ->
  forall x, (A x * den <= a * num <-> opt x <= a).
Proof.
  intros T opt A a num den hA hgap x. destruct (hA x) as [h1 h2]. split.
  - intro h. destruct (hgap x) as [h' | h']; [exact h'|].
    pose proof (Nat.mul_le_mono_r _ _ den h1). lia.
  - intro h. pose proof (Nat.mul_le_mono_r _ _ num h). lia.
Qed.

Record Algo (T : Type) := mkAlgo { run : T -> nat; time : T -> nat }.
Arguments mkAlgo {T} _ _.
Arguments run {T} _ _.
Arguments time {T} _ _.

(** Open obligation (not assumed): a polynomial-time algorithm with ratio
    num/den for the minimisation problem opt. *)
Definition PolyApprox {T : Type} (sz opt : T -> nat) (num den : nat) : Prop :=
  exists (A : Algo T) (c d : nat),
    (forall x, opt x <= run A x /\ run A x * den <= opt x * num) /\
    forall x, time A x <= c * (sz x + 1) ^ d.

(** Conditional theorem: PolyApprox yields a polynomial-time decider for
    every gap promise problem with a larger gap. *)
Theorem polyApprox_decides_gap : forall {T : Type} (sz opt : T -> nat) (a num den : nat),
  PolyApprox sz opt num den ->
  (forall x, opt x <= a \/ a * num < opt x * den) ->
  exists (D : T -> bool) (t : T -> nat) (c d : nat),
    (forall x, D x = true <-> opt x <= a) /\ forall x, t x <= c * (sz x + 1) ^ d.
Proof.
  intros T sz opt a num den [A [c [d [hA hT]]]] hgap.
  exists (fun x => Nat.leb (run A x * den) (a * num)), (time A), c, d. split.
  - intro x. rewrite Nat.leb_le. exact (approx_decides_gap opt (run A) a num den hA hgap x).
  - exact hT.
Qed.
