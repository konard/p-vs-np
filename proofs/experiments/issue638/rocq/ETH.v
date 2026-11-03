(** * Issue #638: the Exponential Time Hypothesis in the shared machine model

    Rocq twin of [proofs/experiments/issue638/lean/ETH.lean]. Declaration
    names match the Lean namespace [Issue638.ETH].

    In October 2026, OpenAI ([openai/math], [SubexponentialSAT]) and
    Anthropic ([anthropics/formal-math], [eth/]) each published a Lean proof
    of a deterministic k-SAT algorithm that runs in time
    [2^{O_k(n polyloglog n / sqrt(log n))}]. Such an algorithm refutes ETH,
    and SETH too, because it works for every fixed k. Their proofs use
    other machine models, and this file does not repeat them. It states ETH
    and SETH over the repository's [Machine] and proves:

    - [pNotEqualsNP_of_eth] and [pNotEqualsNP_of_seth]: P = NP refutes ETH
      and SETH, using the proved [SATVerifier.satInNP];
    - [eth_iff_not_subexp3] and [not_seth_of_subexpAllK]: unfoldings of the
      definitions. The named hypothesis [SubexpKSAT 3] contradicts ETH, and
      [SubexpAllK] contradicts SETH. The labs' theorems are about other
      machine models and are not transported here (P8);
    - [subexpKSAT_of_logBudget] and [logBudget_not_polynomial]: the budget
      [2^{n / (log2 n + 1)}] is subexponential but not polynomially bounded,
      so a subexponential upper bound does not by itself give [InP SAT].
      Whether not-ETH implies P = NP is open; nothing here decides it;
    - [eightSquare] and [eightSquare_cancel]: the eight-square identity
      (Degen 1818, Graves 1843) in the 12-bit form of Anthropic's paper
      ([eth/paper.pdf] at [16a5ce4], eq. (12) and eq. (28)), checked at all
      4096 settings;
    - [swap_eq_id_sub_singlet], [singlet_sq], [swap_sq]: the textbook fact
      SWAP = I - 2 * singlet. It is the identity of the condensed hint in the
      upstream [eth/README.md], not the identity of the paper.

    Model notes: [numVars] is the largest variable index plus one. [Machine]
    has one tape, so [SETH] here may be weaker than the usual RAM form; ETH
    is robust because delta is quantified.

    Not proved here: the sparsification lemma (SETH -> ETH) and any
    simulation between [Machine] and the labs' machine models. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List ZArith Classical_Prop.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines SATVerifier Idea41.

Module ETH.

(** ** k-SAT in exponential time *)

Definition Width (k : nat) (phi : CNF) : Prop :=
  forall c, In c phi -> length c <= k.

Definition DecidesKSATWithin (k : nat) (m : Machine) (T : nat -> nat -> nat) : Prop :=
  forall phi : CNF, Width k phi -> exists t b,
    t <= T (numVars phi) (length (encodeCNF phi)) /\
    Run m (initial (encodeCNF phi)) t b /\ (b = true <-> Satisfiable phi).

Definition expTime (c a d n len : nat) : nat := c * 2 ^ (a * n / d) * (len + 1) ^ c.

Definition KSATExpTime (k a d : nat) : Prop :=
  exists (m : Machine) (c : nat), DecidesKSATWithin k m (expTime c a d).

(** ETH: for some [delta = 1/d > 0], 3-SAT is not decidable in [O*(2^{delta n})]. *)
Definition ETH : Prop := exists d, 0 < d /\ ~ KSATExpTime 3 1 d.

(** SETH: for every [eps = 1/d > 0], some k-SAT is not decidable in [O*(2^{(1-eps) n})]. *)
Definition SETH : Prop := forall d, 0 < d -> exists k, ~ KSATExpTime k (d - 1) d.

Theorem decides_mono : forall k m (T T' : nat -> nat -> nat),
  (forall n len, T n len <= T' n len) ->
  DecidesKSATWithin k m T -> DecidesKSATWithin k m T'.
Proof.
  intros k m T T' hT h phi hphi.
  destruct (h phi hphi) as [t [b [ht [hr hb]]]].
  exists t, b. split; [apply Nat.le_trans with (1 := ht); apply hT | split; assumption].
Qed.

Theorem decides_width_mono : forall k k' m T, k <= k' ->
  DecidesKSATWithin k' m T -> DecidesKSATWithin k m T.
Proof.
  intros k k' m T hk h phi hphi. apply h. intros c hc. specialize (hphi c hc). lia.
Qed.

Theorem ksatExpTime_width_mono : forall k k' a d, k <= k' ->
  KSATExpTime k' a d -> KSATExpTime k a d.
Proof.
  intros k k' a d hk [m [c h]]. exists m, c. exact (decides_width_mono k k' m _ hk h).
Qed.

Theorem exp_div_mono : forall a d a' d' n, 0 < d -> 0 < d' ->
  a * d' <= a' * d -> a * n / d <= a' * n / d'.
Proof.
  intros a d a' d' n hd hd' h.
  apply Nat.div_le_lower_bound; [lia |].
  pose proof (Nat.Div0.mul_div_le (a * n) d) as hq.
  set (q := a * n / d) in *.
  assert (hm : d * (d' * q) <= d * (a' * n)).
  { replace (d * (d' * q)) with (d' * (d * q)) by ring.
    apply Nat.le_trans with (d' * (a * n)); [apply Nat.mul_le_mono_l; exact hq |].
    replace (d' * (a * n)) with (n * (a * d')) by ring.
    replace (d * (a' * n)) with (n * (a' * d)) by ring.
    apply Nat.mul_le_mono_l; exact h. }
  apply Nat.mul_le_mono_pos_l in hm; [exact hm | exact hd].
Qed.

Theorem ksatExpTime_exp_mono : forall k a d a' d', 0 < d -> 0 < d' ->
  a * d' <= a' * d -> KSATExpTime k a d -> KSATExpTime k a' d'.
Proof.
  intros k a d a' d' hd hd' h [m [c hm]]. exists m, c.
  apply (decides_mono k m (expTime c a d)); [| exact hm].
  intros n len. unfold expTime.
  apply Nat.mul_le_mono_r, Nat.mul_le_mono_l, Nat.pow_le_mono_r; [lia |].
  apply exp_div_mono; assumption.
Qed.

(** ** P = NP refutes ETH and SETH *)

Theorem ksatExpTime_of_inP_sat : InP SAT -> forall k a d, KSATExpTime k a d.
Proof.
  intros h k a d.
  destruct (inP_sat_on_encodings h) as [m [p hm]].
  exists m, (coefficient p + degree p). intros phi _.
  destruct (hm phi) as [t [b [ht [hr hb]]]].
  exists t, b. split; [| split; assumption].
  apply Nat.le_trans with (1 := ht). unfold evalPoly, expTime.
  assert (h2 : 1 <= 2 ^ (a * numVars phi / d)) by (apply Nat.le_trans with (2 ^ 0);
    [simpl; lia | apply Nat.pow_le_mono_r; lia]).
  apply Nat.mul_le_mono; [nia |].
  apply Nat.pow_le_mono_r; lia.
Qed.

Theorem not_eth_of_inP_sat : InP SAT -> ~ ETH.
Proof. intros h [d [_ hd]]. exact (hd (ksatExpTime_of_inP_sat h 3 1 d)). Qed.

Theorem not_seth_of_inP_sat : InP SAT -> ~ SETH.
Proof.
  intros h hs. destruct (hs 1 ltac:(lia)) as [k hk].
  exact (hk (ksatExpTime_of_inP_sat h k 0 1)).
Qed.

Theorem not_eth_of_pEqualsNP : PEqualsNP -> ~ ETH.
Proof. intro h. exact (not_eth_of_inP_sat (inP_sat_of_pEqualsNP satInNP h)). Qed.

Theorem pNotEqualsNP_of_eth : ETH -> PNotEqualsNP.
Proof. intros h hp. exact (not_eth_of_pEqualsNP hp h). Qed.

Theorem not_seth_of_pEqualsNP : PEqualsNP -> ~ SETH.
Proof. intro h. exact (not_seth_of_inP_sat (inP_sat_of_pEqualsNP satInNP h)). Qed.

Theorem pNotEqualsNP_of_seth : SETH -> PNotEqualsNP.
Proof. intros h hp. exact (not_seth_of_pEqualsNP hp h). Qed.

(** ** The shape of the October 2026 claims *)

Definition SubexpKSAT (k : nat) : Prop := forall d, 0 < d -> KSATExpTime k 1 d.

Definition SubexpAllK : Prop := forall k, SubexpKSAT k.

Theorem not_eth_of_subexp3 : SubexpKSAT 3 -> ~ ETH.
Proof. intros h [d [hd hn]]. exact (hn (h d hd)). Qed.

(** The converse direction uses excluded middle ([NNPP]), as
    [Classical.byContradiction] does in Lean. *)
Theorem eth_iff_not_subexp3 : ETH <-> ~ SubexpKSAT 3.
Proof.
  split.
  - intros he hs. exact (not_eth_of_subexp3 hs he).
  - intro h. apply NNPP. intro hne. apply h. intros d hd.
    apply NNPP. intro hk. exact (hne (ex_intro _ d (conj hd hk))).
Qed.

Theorem not_seth_of_subexpAllK : SubexpAllK -> ~ SETH.
Proof.
  intros h hs. destruct (hs 2 ltac:(lia)) as [k hk]. exact (hk (h k 2 ltac:(lia))).
Qed.

Theorem subexpKSAT_width_mono : forall k k', k <= k' -> SubexpKSAT k' -> SubexpKSAT k.
Proof. intros k k' hk h d hd. exact (ksatExpTime_width_mono k k' 1 d hk (h d hd)). Qed.

(** ** A subexponential budget that is not polynomial *)

Definition logBudget (n : nat) : nat := 2 ^ (n / (Nat.log2 n + 1)).

Lemma one_le_two_pow : forall e, 1 <= 2 ^ e.
Proof.
  intro e. apply Nat.le_trans with (2 ^ 0); [simpl; lia | apply Nat.pow_le_mono_r; lia].
Qed.

Theorem logBudget_le : forall d n, 0 < d -> logBudget n <= 2 ^ (2 ^ d) * 2 ^ (n / d).
Proof.
  intros d n hd. unfold logBudget.
  pose proof (one_le_two_pow (2 ^ d)) as h1. pose proof (one_le_two_pow (n / d)) as h2.
  destruct (Nat.le_gt_cases (2 ^ d) n) as [h | h].
  - assert (hn : 0 < n) by (pose proof (one_le_two_pow d); lia).
    assert (hl : d <= Nat.log2 n) by (apply Nat.log2_le_pow2; assumption).
    assert (hdiv : n / (Nat.log2 n + 1) <= n / d) by (apply Nat.div_le_compat_l; lia).
    apply Nat.le_trans with (2 ^ (n / d)); [apply Nat.pow_le_mono_r; lia | nia].
  - assert (hdiv : n / (Nat.log2 n + 1) <= 2 ^ d).
    { apply Nat.le_trans with n; [apply Nat.Div0.div_le_upper_bound; nia | lia]. }
    apply Nat.le_trans with (2 ^ (2 ^ d)); [apply Nat.pow_le_mono_r; lia | nia].
Qed.

Theorem subexpKSAT_of_logBudget : forall k m c,
  DecidesKSATWithin k m (fun n len => c * logBudget n * (len + 1) ^ c) -> SubexpKSAT k.
Proof.
  intros k m c h d hd. exists m, (c * 2 ^ (2 ^ d)).
  apply (decides_mono k m (fun n len => c * logBudget n * (len + 1) ^ c)); [| exact h].
  intros n len. unfold expTime. rewrite Nat.mul_1_l.
  pose proof (logBudget_le d n hd) as hb.
  pose proof (one_le_two_pow (2 ^ d)) as h1.
  assert (hpow : (len + 1) ^ c <= (len + 1) ^ (c * 2 ^ (2 ^ d)))
    by (apply Nat.pow_le_mono_r; nia).
  apply Nat.le_trans with (c * (2 ^ (2 ^ d) * 2 ^ (n / d)) * (len + 1) ^ (c * 2 ^ (2 ^ d))).
  - apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l; exact hb | exact hpow].
  - rewrite Nat.mul_assoc. lia.
Qed.

Theorem not_eth_of_logBudget : forall m c,
  DecidesKSATWithin 3 m (fun n len => c * logBudget n * (len + 1) ^ c) -> ~ ETH.
Proof. intros m c h. exact (not_eth_of_subexp3 (subexpKSAT_of_logBudget 3 m c h)). Qed.

Theorem not_seth_of_logBudget :
  (forall k, exists m c,
    DecidesKSATWithin k m (fun n len => c * logBudget n * (len + 1) ^ c)) -> ~ SETH.
Proof.
  intro h. apply not_seth_of_subexpAllK. intro k.
  destruct (h k) as [m [c hm]]. exact (subexpKSAT_of_logBudget k m c hm).
Qed.

Theorem logBudget_two_pow : forall e, logBudget (2 ^ e) = 2 ^ (2 ^ e / (e + 1)).
Proof. intro e. unfold logBudget. rewrite Nat.log2_pow2; [reflexivity | lia]. Qed.

Theorem logBudget_not_polynomial : ~ PolynomiallyBounded logBudget.
Proof.
  intros [a [k h]].
  destruct (poly_le_two_pow (k + a) 2) as [N hN].
  pose proof (h (2 ^ N)) as h1. rewrite logBudget_two_pow in h1.
  assert (hbase : 2 ^ N + 1 <= 2 ^ (N + 1))
    by (rewrite Nat.pow_add_r; pose proof (one_le_two_pow N); simpl; lia).
  assert (h2 : (2 ^ N + 1) ^ k <= 2 ^ ((N + 1) * k))
    by (rewrite Nat.pow_mul_r; apply Nat.pow_le_mono_l; exact hbase).
  assert (h3 : a < 2 ^ a) by (apply Nat.pow_gt_lin_r; lia).
  assert (h4 : a + (N + 1) * k <= 2 ^ N / (N + 1)).
  { apply Nat.div_le_lower_bound; [lia |].
    pose proof (hN N (le_n N)) as hN'.
    apply Nat.le_trans with ((k + a) * (N + 1) ^ 2); [| exact hN'].
    rewrite Nat.pow_2_r.
    assert (ha : a <= (N + 1) * a) by nia.
    apply Nat.le_trans with ((N + 1) * ((N + 1) * a + (N + 1) * k)); [nia |].
    apply Nat.eq_le_incl. ring. }
  assert (h5 : a * 2 ^ ((N + 1) * k) < 2 ^ (a + (N + 1) * k)).
  { rewrite Nat.pow_add_r. apply Nat.mul_lt_mono_pos_r; [| exact h3].
    pose proof (one_le_two_pow ((N + 1) * k)). lia. }
  assert (h6 : 2 ^ (a + (N + 1) * k) <= 2 ^ (2 ^ N / (N + 1)))
    by (apply Nat.pow_le_mono_r; lia).
  assert (h7 : a * (2 ^ N + 1) ^ k <= a * 2 ^ ((N + 1) * k))
    by (apply Nat.mul_le_mono_l; exact h2).
  lia.
Qed.

Theorem logBudget_gap :
  (forall d, 0 < d -> exists C, forall n, logBudget n <= C * 2 ^ (n / d)) /\
  ~ PolynomiallyBounded logBudget.
Proof.
  split; [| exact logBudget_not_polynomial].
  intros d hd. exists (2 ^ (2 ^ d)). intro n. exact (logBudget_le d n hd).
Qed.

(** ** The eight-square identity of Anthropic's paper

    [eth/paper.pdf] at [16a5ce4], section 2.4: for blocks [p, q] in
    [{0,1}^3], [sigma(p,q) = (-1)^{phi(p,q)}] with
    [phi(p,q) = sum_{i <= j} p_i q_j + q1 p2 p3 + p1 q2 p3 + p1 p2 q3].
    A block is a number below 8, and bit [i - 1] of it is [p_i]. These
    theorems check the identity only, not Lemma 2 or the algorithm. *)

Open Scope Z_scope.

Definition bit (p k : nat) : nat := (p / 2 ^ k) mod 2.

Definition phi (p q : nat) : nat :=
  (bit p 0 * bit q 0 + bit p 0 * bit q 1 + bit p 0 * bit q 2 +
   bit p 1 * bit q 1 + bit p 1 * bit q 2 + bit p 2 * bit q 2 +
   bit q 0 * bit p 1 * bit p 2 + bit p 0 * bit q 1 * bit p 2 +
   bit p 0 * bit p 1 * bit q 2)%nat.

Definition sigma (p q : nat) : Z := if Nat.even (phi p q) then 1 else -1.

Definition ind (b : bool) : Z := if b then 1 else 0.

Definition xor4 (x y u v : nat) : nat := Nat.lxor (Nat.lxor (Nat.lxor x y) u) v.

Definition below8 (f : nat -> bool) : bool := forallb f (seq 0 8).

Lemma below8_spec : forall f, below8 f = true -> forall i, (i < 8)%nat -> f i = true.
Proof.
  intros f h i hi. unfold below8 in h. rewrite forallb_forall in h.
  apply h. apply in_seq. lia.
Qed.

Definition eightSquare_at (x y u v : nat) : bool :=
  Z.eqb (2 * ind (Nat.eqb x v) * ind (Nat.eqb y u))
        (ind (Nat.eqb (xor4 x y u v) 0) * (sigma x y * sigma v u + sigma x u * sigma v y)).

Definition eightSquare_cancel_at (p q p' q' : nat) : bool :=
  implb (Nat.eqb (Nat.lxor p q) (Nat.lxor p' q') && negb (Nat.eqb q q'))
        (Z.eqb (sigma p q * sigma p' q' + sigma p q' * sigma p' q) 0).

Lemma eightSquare_all : below8 (fun x => below8 (fun y => below8 (fun u =>
  below8 (fun v => eightSquare_at x y u v)))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma eightSquare_cancel_all : below8 (fun p => below8 (fun q => below8 (fun p' =>
  below8 (fun q' => eightSquare_cancel_at p q p' q')))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Eq. (12) of the paper:
    [2 [x = v] [y = u] = [x xor y xor u xor v = 0] (sigma(x,y) sigma(v,u) + sigma(x,u) sigma(v,y))]. *)
Theorem eightSquare : forall x y u v : nat,
  (x < 8)%nat -> (y < 8)%nat -> (u < 8)%nat -> (v < 8)%nat ->
  2 * ind (Nat.eqb x v) * ind (Nat.eqb y u) =
    ind (Nat.eqb (xor4 x y u v) 0) * (sigma x y * sigma v u + sigma x u * sigma v y).
Proof.
  intros x y u v hx hy hu hv. apply Z.eqb_eq.
  exact (below8_spec _ (below8_spec _ (below8_spec _
    (below8_spec _ eightSquare_all x hx) y hy) u hu) v hv).
Qed.

(** Eq. (28) of the paper: if [p xor q = p' xor q'] and [q <> q'], then
    [sigma(p,q) sigma(p',q') + sigma(p,q') sigma(p',q) = 0]. *)
Theorem eightSquare_cancel : forall p q p' q' : nat,
  (p < 8)%nat -> (q < 8)%nat -> (p' < 8)%nat -> (q' < 8)%nat ->
  Nat.lxor p q = Nat.lxor p' q' -> q <> q' ->
  sigma p q * sigma p' q' + sigma p q' * sigma p' q = 0.
Proof.
  intros p q p' q' hp hq hp' hq' hx hne.
  pose proof (below8_spec _ (below8_spec _ (below8_spec _
    (below8_spec _ eightSquare_cancel_all p hp) q hq) p' hp') q' hq') as h.
  unfold eightSquare_cancel_at in h.
  apply Nat.eqb_eq in hx. rewrite hx in h.
  apply Nat.eqb_neq in hne. rewrite hne in h. simpl in h.
  apply Z.eqb_eq. exact h.
Qed.

(** ** The textbook SWAP identity of the upstream README's condensed hint

    [eth/README.md] gives a condensed form of the idea in terms of
    SWAP = I - 2 * singlet and a [12^lambda] rank bound. The paper is built
    on the eight-square identity above instead. *)

(** Basis index [2a + b] for the two bits [(a, b)]. *)
Definition swapM (i j : nat) : Z :=
  if Nat.eqb j (match i with 1%nat => 2%nat | 2%nat => 1%nat | v => v end) then 1 else 0.

Definition idM (i j : nat) : Z := if Nat.eqb i j then 1 else 0.

(** The singlet vector [|01> - |10>]; twice the singlet projector is [u u^T]. *)
Definition u (i : nat) : Z := match i with 1%nat => 1 | 2%nat => -1 | _ => 0 end.

Definition singlet2 (i j : nat) : Z := u i * u j.

Definition mul4 (A B : nat -> nat -> Z) (i j : nat) : Z :=
  A i 0%nat * B 0%nat j + A i 1%nat * B 1%nat j +
  A i 2%nat * B 2%nat j + A i 3%nat * B 3%nat j.

Ltac four i := destruct i as [| [| [| [| i]]]]; [| | | | exfalso; lia].

Theorem swap_eq_id_sub_singlet : forall i j : nat, (i < 4)%nat -> (j < 4)%nat ->
  swapM i j = idM i j - singlet2 i j.
Proof. intros i j hi hj. four i; four j; reflexivity. Qed.

Theorem singlet_sq : forall i j : nat, (i < 4)%nat -> (j < 4)%nat ->
  mul4 singlet2 singlet2 i j = 2 * singlet2 i j.
Proof. intros i j hi hj. four i; four j; reflexivity. Qed.

Theorem swap_sq : forall i j : nat, (i < 4)%nat -> (j < 4)%nat ->
  mul4 swapM swapM i j = idM i j.
Proof. intros i j hi hj. four i; four j; reflexivity. Qed.

End ETH.
