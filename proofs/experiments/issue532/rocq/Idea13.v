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
   (approx_decides_gap).

   Over the shared machine model (Machines.v): the open obligation
   PolyApprox (a Machine computing, in the sense of Computes, a word whose
   value wordValue is a num/den-approximation), the conditional theorem
   polyApprox_decides_gap, and the non-vacuity theorem not_forall_polyApprox.

   Difference from Lean: the Lean thresholdLanguage num m is noncomputable
   (it decides, classically, a statement about all functions m computes).
   Here thresholdLanguage num (m, p) is computable: it runs m for p(|x|)
   steps with the interpreter runOut and reads the output word off the tape
   (thresholdLanguage_computes shows it agrees with the Lean one on every
   machine that computes a function within p).  The diagonalisation is then
   against (machine, polynomial) pairs, and it is done pointwise because Rocq
   has no function extensionality here.  No axioms are used.

   Verdict: approximation gives exactness only below an integrality gap; the
   open obligation PolyApprox beyond a published NP-hardness threshold would
   itself prove P = NP.  Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(** ** The obligation over the shared machine model

    An approximation algorithm is a [Machine] that computes (in the sense of
    [Computes], with the step count of the run as its time) a binary word
    whose value is the approximate optimum.  Instances are words. *)

(** Value of a binary word, least significant bit first. *)
Fixpoint wordValue (w : Word) : nat :=
  match w with
  | [] => 0
  | b :: w' => (if b then 1 else 0) + 2 * wordValue w'
  end.

(** Open obligation.  A polynomial-time machine that outputs, for every
    instance x, a value A x with opt x <= A x and A x * den <= opt x * num
    (ratio num/den for the minimisation problem opt).  For problems and
    ratios below a published NP-hardness-of-approximation threshold, this
    statement implies P = NP (via approx_decides_gap and the corresponding
    PCP reduction). *)
Definition PolyApprox (opt : Word -> nat) (num den : nat) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, opt x <= wordValue (f x) /\ wordValue (f x) * den <= opt x * num.

(** Conditional theorem: PolyApprox for ratio num/den gives a polynomial-time
    machine whose output answers every gap promise problem with gap larger
    than num/den by the single comparison A x * den <= a * num. *)
Theorem polyApprox_decides_gap : forall (opt : Word -> nat) (a num den : nat),
  PolyApprox opt num den ->
  (forall x, opt x <= a \/ a * num < opt x * den) ->
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, (wordValue (f x) * den <= a * num <-> opt x <= a).
Proof.
  intros opt a num den [m [f [p [hm hA]]]] hgap.
  exists m, f, p. split; [exact hm |].
  exact (approx_decides_gap opt (fun x => wordValue (f x)) a num den hA hgap).
Qed.

(** A language as a minimisation problem: optimum 1 on members and num + 1
    on non-members. *)
Definition optOf (L : Language) (num : nat) (x : Word) : nat :=
  if L x then 1 else num + 1.

(** ** Reading a machine's output (computable) *)

(** Run [m] from [c] for at most [fuel] steps until it reaches the exit state
    [length (program m)]; return that configuration. *)
Fixpoint runOut (m : Machine) (c : Config) (fuel : nat) : option Config :=
  if Nat.eqb (state c) (length (program m)) then Some c else
  match fuel with
  | 0 => None
  | S f => match step m c with
           | inl _ => None
           | inr c' => runOut m c' f
           end
  end.

Lemma runOut_of_reaches : forall m c t d, Reaches m c t d ->
  state d = length (program m) -> forall fuel, t <= fuel -> runOut m c fuel = Some d.
Proof.
  intros m c t d h. induction h as [c | c c' d t hs hr IH]; intros hd fuel hf.
  - destruct fuel; simpl; rewrite hd, Nat.eqb_refl; reflexivity.
  - pose proof (state_lt_of_step _ _ _ hs) as hlt.
    destruct fuel as [| fuel]; [lia |]. simpl.
    destruct (Nat.eqb_spec (state c) (length (program m))) as [e | _]; [lia |].
    rewrite hs. apply IH; [exact hd | lia].
Qed.

(** The bits at the head and to its right, up to the first non-bit symbol. *)
Fixpoint readBits (l : list Symbol) : Word :=
  match l with
  | one :: r => true :: readBits r
  | zero :: r => false :: readBits r
  | _ => []
  end.

Lemma readBits_output : forall w k, readBits (map ofBool w ++ blanks k) = w.
Proof.
  intros w k. induction w as [| b w IH]; simpl.
  - destruct k; reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

(** The language read off the output of [m], run for [p(|x|)] steps, by the
    threshold test [wordValue <= num]. *)
Definition thresholdLanguage (num : nat) (x : Machine * Polynomial) : Language :=
  fun w =>
    match runOut (fst x) (initial w) (evalPoly (snd x) (length w)) with
    | Some c => Nat.leb (wordValue (readBits (tapeHead c :: tapeRight c))) num
    | None => false
    end.

(** On a machine that computes [f] within [p], [thresholdLanguage] is the
    threshold test on [f]. *)
Theorem thresholdLanguage_computes : forall num m f p, Computes m f p ->
  forall x, thresholdLanguage num (m, p) x = Nat.leb (wordValue (f x)) num.
Proof.
  intros num m f p hm x. destruct (hm x) as [t [c [ht [hr [hs [_ [k hk]]]]]]].
  unfold thresholdLanguage. cbn [fst snd].
  rewrite (runOut_of_reaches _ _ _ _ hr hs _ ht), hk, readBits_output.
  reflexivity.
Qed.

(** Non-vacuity.  For every ratio with den >= 1, some problem has no
    polynomial-time machine approximation: PolyApprox is not provable for
    every opt. *)
Theorem not_forall_polyApprox : forall num den, 1 <= den ->
  ~ (forall opt : Word -> nat, PolyApprox opt num den).
Proof.
  intros num den hden hall.
  set (L := fun w : Word => match decMachinePoly w with
                            | Some a => negb (thresholdLanguage num a w)
                            | None => true
                            end).
  destruct (hall (optOf L num)) as [m [f [p [hm hA]]]].
  set (w := encMachinePoly (m, p)).
  assert (hL : L w = negb (Nat.leb (wordValue (f w)) num)).
  { unfold L, w. rewrite (decMachinePoly_encMachinePoly (m, p)).
    rewrite (thresholdLanguage_computes num m f p hm). reflexivity. }
  destruct (hA w) as [h1 h2]. unfold optOf in h1, h2.
  assert (hmul : wordValue (f w) <= wordValue (f w) * den) by nia.
  destruct (L w) eqn:hLw.
  - destruct (Nat.leb_spec (wordValue (f w)) num) as [hle | hgt];
      simpl in hL; [discriminate | lia].
  - destruct (Nat.leb_spec (wordValue (f w)) num) as [hle | hgt];
      simpl in hL; [lia | discriminate].
Qed.
