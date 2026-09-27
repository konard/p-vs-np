(* Issue #532, Idea 14: randomized search.

   Rocq counterpart of lean/Idea14.lean; theorem names are aligned.

   A randomized algorithm on input x is a function A x : nat -> bool of a
   seed i < s x.  cnt s P counts seeds i < s with P i; countT s k Q counts
   length-k seed tuples over [0, s) satisfying Q by honest enumeration.
   Proved in general: s^k tuples (countT_true), (cnt s P)^k all-P tuples
   (countT_all), one-sided amplification (amplification_count,
   rp_amplification, one_sided_amplified), observed success is no guarantee
   (observed_success_no_guarantee), derandomization by seed enumeration and
   its cost (enumeration_decides, poly_seeds_derandomize).

   Over the shared machine model (Machines.v; a randomised machine runs on
   pairedInput x r for a random string r, and its time is the step count of
   Run): seedWord, seedWord_surjective, two_pow_logSeed; HaltsWithin,
   RPMachine, InRP, PolySeedMachine, PolySeedRP; the open obligations
   NPinRP := InRP SAT and SeedCompression; the named known theorem
   SeedEnumeration (a premise only) with its mathematical core
   logSeed_enumeration; the conditional theorems
   rp_sat_with_seed_compression and rp_route_gives_pEqualsNP; and the
   non-vacuity theorem not_forall_inRP.

   Differences from Lean:
   - The Lean seedAccepts m l x i is noncomputable (it decides classically
     whether some run accepts).  Here seedAccepts m p l x i is computable: it
     runs m with the step-bounded interpreter runFor for the time bound
     p(|x| + l |x| + 1) that HaltsWithin grants.  seedAccepts_iff shows that
     under HaltsWithin it is exactly the Lean predicate "some run accepts".
     Accordingly rpLanguage is indexed by triples (m, p, R), encoded by
     encRPMachine with the left inverse decRPMachine.
   - The diagonalisation in not_forall_inRP is pointwise (Rocq has no
     function extensionality here).  No axioms are used.

   Verdict: randomness changes the target class; returning to P needs an
   open derandomization step.  NPinRP and SeedCompression are definitions,
   never assumed.  Nothing here proves or refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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


(** ** The obligations over the shared machine model

    A randomised decider is a [Machine] run on [pairedInput x r] for a random
    string [r]; its time is the step count of [Run].  The random-string length
    is an explicit polynomial [R] (for RP) or [k * log2 (n+1)] (for
    seed-compressed algorithms); it is never an arbitrary function of the
    input length, which would smuggle in advice. *)

(** The [i]-th random string of length [l] (binary, least significant bit
    first). *)
Fixpoint seedWord (l i : nat) : Word :=
  match l with
  | 0 => []
  | S l' => Nat.eqb (i mod 2) 1 :: seedWord l' (i / 2)
  end.

Theorem seedWord_length : forall l i, length (seedWord l i) = l.
Proof. induction l as [| l IH]; intro i; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Seeds [i < 2^l] enumerate every random string of length [l]. *)
Theorem seedWord_surjective : forall r : Word,
  exists i, i < 2 ^ length r /\ seedWord (length r) i = r.
Proof.
  induction r as [| b r IH].
  - exists 0. simpl. split; [lia | reflexivity].
  - destruct IH as [i [hi hr]].
    exists (2 * i + (if b then 1 else 0)). simpl length. rewrite Nat.pow_succ_r'.
    split; [destruct b; lia |].
    change (seedWord (S (length r)) (2 * i + (if b then 1 else 0))) with
      (Nat.eqb ((2 * i + (if b then 1 else 0)) mod 2) 1 ::
       seedWord (length r) ((2 * i + (if b then 1 else 0)) / 2)).
    assert (hd : (2 * i + (if b then 1 else 0)) / 2 = i).
    { rewrite Nat.mul_comm, Nat.div_add_l by lia.
      destruct b; [change (1 / 2) with 0 | change (0 / 2) with 0]; lia. }
    assert (hm : (2 * i + (if b then 1 else 0)) mod 2 = if b then 1 else 0).
    { rewrite Nat.mul_comm, Nat.add_comm, Nat.Div0.mod_add. destruct b; reflexivity. }
    rewrite hd, hm, hr. destruct b; reflexivity.
Qed.

(** [m] halts within [p] on input [x] with every random string of length
    [l(|x|)]. *)
Definition HaltsWithin (m : Machine) (p : Polynomial) (l : nat -> nat) : Prop :=
  forall x i, exists t b, t <= evalPoly p (length x + l (length x) + 1) /\
    Run m (pairedInput x (seedWord (l (length x)) i)) t b.

(** Seed [i] makes [m] accept [x] within the time bound of [HaltsWithin]
    (computable: the step-bounded interpreter [runFor] of Machines.v). *)
Definition seedAccepts (m : Machine) (p : Polynomial) (l : nat -> nat) (x : Word) (i : nat) : bool :=
  match runFor m (pairedInput x (seedWord (l (length x)) i))
      (evalPoly p (length x + l (length x) + 1)) with
  | Some true => true
  | _ => false
  end.

(** Under [HaltsWithin], [seedAccepts] is the Lean predicate "some run on
    this seed accepts". *)
Theorem seedAccepts_iff : forall m p l, HaltsWithin m p l -> forall x i,
  seedAccepts m p l x i = true <->
  exists t, Run m (pairedInput x (seedWord (l (length x)) i)) t true.
Proof.
  intros m p l h x i. destruct (h x i) as [t [b [ht hr]]].
  unfold seedAccepts. rewrite (runFor_of_run _ _ _ _ hr _ ht). split.
  - intro hb. destruct b; [exists t; exact hr | discriminate].
  - intros [t' hr']. destruct (run_deterministic _ _ _ _ _ _ hr hr') as [_ ->].
    reflexivity.
Qed.

(** A polynomial-time one-sided randomised machine for [L]: random strings of
    length [R(|x|)], never accepts a no-instance, accepts a yes-instance on at
    least half of the random strings. *)
Definition RPMachine (m : Machine) (p R : Polynomial) (L : Language) : Prop :=
  HaltsWithin m p (evalPoly R) /\
  OneSided L (seedAccepts m p (evalPoly R)) (fun x => 2 ^ evalPoly R (length x)).

(** The class RP of the shared machine model. *)
Definition InRP (L : Language) : Prop :=
  exists (m : Machine) (p R : Polynomial), RPMachine m p R L.

(** Open obligation.  SAT has a polynomial-time one-sided randomised machine
    decider (NP is contained in RP). *)
Definition NPinRP : Prop := InRP SAT.

(** Logarithmic seed length [k * log2 (n+1)]. *)
Definition logSeed (k n : nat) : nat := k * Nat.log2 (n + 1).

(** Logarithmic seeds are polynomially many. *)
Theorem two_pow_logSeed : forall k n, 2 ^ logSeed k n <= (n + 1) ^ k.
Proof.
  intros k n. unfold logSeed. rewrite Nat.mul_comm, Nat.pow_mul_r.
  apply Nat.pow_le_mono_l. apply Nat.log2_spec. lia.
Qed.

(** A polynomial-time one-sided randomised machine with logarithmic seeds. *)
Definition PolySeedMachine (m : Machine) (p : Polynomial) (k : nat) (L : Language) : Prop :=
  HaltsWithin m p (logSeed k) /\
  OneSided L (seedAccepts m p (logSeed k)) (fun x => 2 ^ logSeed k (length x)).

Definition PolySeedRP (L : Language) : Prop :=
  exists (m : Machine) (p : Polynomial) (k : nat), PolySeedMachine m p k L.

(** Open obligation.  Seed compression for [L]: a polynomial-time one-sided
    randomised machine can be replaced by one with logarithmic seeds (what a
    suitable pseudorandom generator provides). *)
Definition SeedCompression (L : Language) : Prop := InRP L -> PolySeedRP L.

(** Known theorem, not mechanised here (derandomization by enumeration, Gill
    1977): a machine that tries all [2^(k log2 (n+1)) <= (n+1)^k] seeds, each
    run within [p], decides [L] deterministically in polynomial time.  The
    mathematics is [logSeed_enumeration]; the missing part is the
    single-tape machine that enumerates the seeds and simulates [m].  Used
    only as an explicit premise. *)
Definition SeedEnumeration : Prop := forall L, PolySeedRP L -> InP L.

(** The mathematical core of [SeedEnumeration]: trying every seed gives the
    right answer, there are at most [(n+1)^k] seeds, and each run halts
    within [p(n + k log2 (n+1) + 1)] steps. *)
Theorem logSeed_enumeration : forall m p k L, PolySeedMachine m p k L ->
  forall x,
    anySeed (2 ^ logSeed k (length x)) (seedAccepts m p (logSeed k) x) = L x /\
    2 ^ logSeed k (length x) <= (length x + 1) ^ k /\
    forall i, exists t b, t <= evalPoly p (length x + logSeed k (length x) + 1) /\
      Run m (pairedInput x (seedWord (logSeed k (length x)) i)) t b.
Proof.
  intros m p k L [hh ho] x. split; [| split].
  - exact (enumeration_decides L _ _ ho x).
  - apply two_pow_logSeed.
  - exact (hh x).
Qed.

(** Conditional theorem: [NPinRP], [SeedCompression SAT] and the known
    [SeedEnumeration] give a polynomial-time machine decider for SAT. *)
Theorem rp_sat_with_seed_compression :
  NPinRP -> SeedCompression SAT -> SeedEnumeration -> PolyDec SAT.
Proof. intros h1 h2 h3. apply polyDec_iff_inP. exact (h3 SAT (h2 h1)). Qed.

(** With the hardness half of Cook-Levin the conclusion is P = NP. *)
Theorem rp_route_gives_pEqualsNP :
  NPinRP -> SeedCompression SAT -> SeedEnumeration -> SATHard -> PEqualsNP.
Proof. intros h1 h2 h3 hard. exact (pEqualsNP_of_inP_sat hard (h3 SAT (h2 h1))). Qed.

(** The language a one-sided randomised machine decides is determined by the
    machine, its time bound and the random-string length. *)
Definition rpLanguage (x : Machine * Polynomial * Polynomial) : Language :=
  fun w => anySeed (2 ^ evalPoly (snd x) (length w))
    (seedAccepts (fst (fst x)) (snd (fst x)) (evalPoly (snd x)) w).

(** Encoding of (machine, time bound, random-string length) triples. *)
Definition encRPMachine (x : Machine * Polynomial * Polynomial) : Word :=
  encMachine (fst (fst x)) ++ encNat (coefficient (snd (fst x))) ++
  encNat (degree (snd (fst x))) ++ encNat (coefficient (snd x)) ++
  encNat (degree (snd x)).

(** Its left inverse (trailing bits are ignored). *)
Definition decRPMachine (w : Word) : option (Machine * Polynomial * Polynomial) :=
  obind (decMachineFront w) (fun '(m, r1) =>
  obind (decNat r1) (fun '(c, r2) =>
  obind (decNat r2) (fun '(k, r3) =>
  obind (decNat r3) (fun '(c', r4) =>
  obind (decNat r4) (fun '(k', _) =>
  Some (m, {| coefficient := c; degree := k |},
        {| coefficient := c'; degree := k' |})))))).

Theorem decRPMachine_encRPMachine : forall x, decRPMachine (encRPMachine x) = Some x.
Proof.
  intros [[m [c k]] [c' k']]. unfold decRPMachine, encRPMachine. simpl.
  rewrite decMachineFront_encMachine. simpl.
  rewrite decNat_encNat. simpl. rewrite decNat_encNat. simpl.
  rewrite decNat_encNat. simpl.
  rewrite <- (app_nil_r (encNat k')), decNat_encNat. reflexivity.
Qed.

(** Non-vacuity.  [InRP] does not hold for every language, so [NPinRP] is a
    statement about SAT, not a consequence of the definitions. *)
Theorem not_forall_inRP : ~ (forall L : Language, InRP L).
Proof.
  intro hall.
  set (L := fun w : Word => match decRPMachine w with
                            | Some a => negb (rpLanguage a w)
                            | None => true
                            end).
  destruct (hall L) as [m [p [R [_ hone]]]].
  set (w := encRPMachine (m, p, R)).
  pose proof (enumeration_decides L _ _ hone w) as he.
  assert (hL : L w = negb (rpLanguage (m, p, R) w)).
  { unfold L, w. rewrite decRPMachine_encRPMachine. reflexivity. }
  unfold rpLanguage in hL. cbn [fst snd] in hL. rewrite he in hL.
  destruct (L w); discriminate.
Qed.
