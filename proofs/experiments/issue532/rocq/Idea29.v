(** * Issue #532, Idea 29: reduction chains and polynomial composition

    Rocq counterpart of [lean/Idea29.lean]; theorem names are aligned (Lean
    dotted names map to [eval_mono], [add_bound], [comp_bound],
    [reduction_comp], [reduction_id], [toPolynomial], [eval_toPolynomial],
    [polymap_comp], [polymap_ident], [polyred_comp], [polyred_comp_fn],
    [pullback]).

    Verdict: correct tool, insufficient alone (general theorem proved).

    Polynomial-time many-one reductions compose.  In the shared machine model
    [Machines.v] a reduction is [PolyReduces L L'].  This file proves that
    machine reductions form a preorder ([polyReduces_refl],
    [polyReduces_trans], via the concatenated table [appendMachine] in
    [computes_comp]), so membership in P is inherited backwards along chains
    ([inP_of_chain]) and any class closed under reductions that contains an
    NP-hard language contains NP ([closed_contains_np]).

    The open obligation of the "reduce NP to P" route, stated in the machine
    model, is [SATReducesToP := exists L', PolyReduces SAT L' /\ InP L'], and
    [satReducesToP_iff_inP_sat] proves it equivalent to [InP SAT].  It yields
    P = NP only under the named premise [SATHard]
    ([pEqualsNP_of_satReducesToP]); [satReducesToP_iff_pEqualsNP] needs
    [CookLevin].  Non-vacuity: [not_forall_reducesToP].  Nothing here decides
    P vs NP.

    The explicit polynomials [Poly] ([eval n = coef * (n + 1) ^ deg], the
    same shape as the shared [Polynomial], see [eval_toPolynomial]) are closed
    under addition and substitution.  The earlier abstract model, in which a
    map carries a declared cost function, is kept as a schema ([PolyMapFor],
    [PolyReductionFor], [PolyDeciderFor], [InPFor], [ReducesToPFor], ...);
    [inPFor_every] shows that the schema alone makes every decidable language
    "polynomial-time", and [inPFor_of_inP] instantiates it with the machine
    step count.  No axioms are used. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** ** Explicit polynomials *)

(** Explicit polynomial bound [coef * (n + 1) ^ deg].  (The Lean fields are
    [coefficient] and [degree]; they are renamed here because the shared
    [Polynomial] record already owns those projection names.) *)
Record Poly := mkPoly { coef : nat; deg : nat }.

Definition eval (p : Poly) (n : nat) : nat :=
  coef p * (n + 1) ^ deg p.

Definition poly_add (p q : Poly) : Poly :=
  mkPoly (coef p + coef q) (Nat.max (deg p) (deg q)).

Definition poly_comp (p q : Poly) : Poly :=
  mkPoly (coef q * (coef p + 1) ^ deg q) (deg p * deg q).

Definition poly_linear : Poly := mkPoly 1 1.
Definition poly_zero : Poly := mkPoly 0 0.

Lemma pow_pos_succ (n k : nat) : 1 <= (n + 1) ^ k.
Proof.
  assert (H : (n + 1) ^ k <> 0) by (apply Nat.pow_nonzero; lia). lia.
Qed.

(** Explicit polynomials are monotone in the input length. *)
Theorem eval_mono (p : Poly) (m n : nat) : m <= n -> eval p m <= eval p n.
Proof.
  intro H. unfold eval. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l. lia.
Qed.

(** Closure under addition. *)
Theorem add_bound (p q : Poly) (n : nat) :
  eval p n + eval q n <= eval (poly_add p q) n.
Proof.
  unfold eval, poly_add; simpl.
  assert (hp : (n + 1) ^ deg p <= (n + 1) ^ Nat.max (deg p) (deg q))
    by (apply Nat.pow_le_mono_r; [lia | apply Nat.le_max_l]).
  assert (hq : (n + 1) ^ deg q <= (n + 1) ^ Nat.max (deg p) (deg q))
    by (apply Nat.pow_le_mono_r; [lia | apply Nat.le_max_r]).
  rewrite Nat.mul_add_distr_r.
  apply Nat.add_le_mono; apply Nat.mul_le_mono_l; assumption.
Qed.

(** Closure under composition: q (p n) <= (poly_comp p q) n. *)
Theorem comp_bound (p q : Poly) (n : nat) :
  eval q (eval p n) <= eval (poly_comp p q) n.
Proof.
  unfold eval, poly_comp; simpl.
  pose proof (pow_pos_succ n (deg p)) as hX.
  assert (h1 : coef p * (n + 1) ^ deg p + 1
               <= (coef p + 1) * (n + 1) ^ deg p) by lia.
  assert (h2 : (coef p * (n + 1) ^ deg p + 1) ^ deg q
               <= ((coef p + 1) * (n + 1) ^ deg p) ^ deg q)
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

(** Correctness of reductions composes. *)
Theorem reduction_comp {A B C : Type} (f : A -> B) (g : B -> C)
  (L : A -> Prop) (M : B -> Prop) (N : C -> Prop) :
  IsReduction f L M -> IsReduction g M N -> IsReduction (fun x => g (f x)) L N.
Proof.
  intros hf hg x. rewrite (hf x). apply hg.
Qed.

Theorem reduction_id {A : Type} (L : A -> Prop) : IsReduction (fun x => x) L L.
Proof. intro x. reflexivity. Qed.

(** The explicit polynomial as a shared [Polynomial]. *)
Definition toPolynomial (p : Poly) : Polynomial :=
  {| coefficient := coef p; degree := deg p |}.

(** [eval] is the shared [evalPoly]. *)
Theorem eval_toPolynomial (p : Poly) (n : nat) : evalPoly (toPolynomial p) n = eval p n.
Proof. reflexivity. Qed.

(** ** Abstract cost schema

    A schema, not a statement about the machine model: a map or a decider
    carries a declared cost function, so nothing ties the cost to a
    computation.  [inPFor_every] makes this explicit, and [inPFor_of_inP]
    instantiates the schema with the machine step count. *)

Record PolyMapFor {A B : Type} (sa : A -> nat) (sb : B -> nat) := mkPolyMapFor {
  pm_fn : A -> B;
  pm_time : A -> nat;
  pm_timeBound : Poly;
  pm_sizeBound : Poly;
  pm_time_le : forall x, pm_time x <= eval pm_timeBound (sa x);
  pm_size_le : forall x, sb (pm_fn x) <= eval pm_sizeBound (sa x)
}.
Arguments mkPolyMapFor {A B sa sb}.
Arguments pm_fn {A B sa sb}.
Arguments pm_time {A B sa sb}.
Arguments pm_timeBound {A B sa sb}.
Arguments pm_sizeBound {A B sa sb}.
Arguments pm_time_le {A B sa sb}.
Arguments pm_size_le {A B sa sb}.

(** Schema: running [f] then [g]: time is the sum, bounds are explicit. *)
Definition polymap_comp {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  (f : PolyMapFor sa sb) (g : PolyMapFor sb sc) : PolyMapFor sa sc.
Proof.
  refine (mkPolyMapFor (fun x => pm_fn g (pm_fn f x))
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

(** The time of a composed chain of polynomially bounded maps is polynomial. *)
Theorem comp_time_poly_for {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  (f : PolyMapFor sa sb) (g : PolyMapFor sb sc) :
  exists r : Poly, forall x, pm_time f x + pm_time g (pm_fn f x) <= eval r (sa x).
Proof.
  exists (pm_timeBound (polymap_comp f g)). intro x.
  exact (pm_time_le (polymap_comp f g) x).
Qed.

Definition polymap_ident {A : Type} (sa : A -> nat) : PolyMapFor sa sa.
Proof.
  refine (mkPolyMapFor (fun x => x) (fun _ => 0) poly_zero poly_linear _ _).
  - intro x. lia.
  - intro x. unfold eval, poly_linear; simpl. lia.
Defined.

Record PolyReductionFor {A B : Type} (sa : A -> nat) (sb : B -> nat)
  (L : A -> Prop) (M : B -> Prop) := mkPolyReductionFor {
  pr_map : PolyMapFor sa sb;
  pr_correct : IsReduction (pm_fn pr_map) L M
}.
Arguments mkPolyReductionFor {A B sa sb L M}.
Arguments pr_map {A B sa sb L M}.
Arguments pr_correct {A B sa sb L M}.

(** Polynomially bounded reductions compose. *)
Definition polyred_comp {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  {L : A -> Prop} {M : B -> Prop} {N : C -> Prop}
  (f : PolyReductionFor sa sb L M) (g : PolyReductionFor sb sc M N) :
  PolyReductionFor sa sc L N :=
  mkPolyReductionFor (polymap_comp (pr_map f) (pr_map g))
    (reduction_comp _ _ L M N (pr_correct f) (pr_correct g)).

(** The composed reduction computes g after f. *)
Theorem polyred_comp_fn {A B C : Type} {sa : A -> nat} {sb : B -> nat} {sc : C -> nat}
  {L : A -> Prop} {M : B -> Prop} {N : C -> Prop}
  (f : PolyReductionFor sa sb L M) (g : PolyReductionFor sb sc M N) :
  forall x, pm_fn (pr_map (polyred_comp f g)) x = pm_fn (pr_map g) (pm_fn (pr_map f) x).
Proof. reflexivity. Qed.

Record PolyDeciderFor {A : Type} (sa : A -> nat) (L : A -> Prop) := mkPolyDeciderFor {
  pd_decide : A -> bool;
  pd_time : A -> nat;
  pd_bound : Poly;
  pd_correct : forall x, L x <-> pd_decide x = true;
  pd_time_le : forall x, pd_time x <= eval pd_bound (sa x)
}.
Arguments mkPolyDeciderFor {A sa L}.
Arguments pd_decide {A sa L}.
Arguments pd_time {A sa L}.
Arguments pd_bound {A sa L}.
Arguments pd_correct {A sa L}.
Arguments pd_time_le {A sa L}.

Definition InPFor {A : Type} (sa : A -> nat) (L : A -> Prop) : Prop :=
  inhabited (PolyDeciderFor sa L).

(** Pull a decider back along a polynomially bounded reduction. *)
Definition pullback {A B : Type} {sa : A -> nat} {sb : B -> nat}
  {L : A -> Prop} {M : B -> Prop}
  (r : PolyReductionFor sa sb L M) (d : PolyDeciderFor sb M) : PolyDeciderFor sa L.
Proof.
  refine (mkPolyDeciderFor (fun x => pd_decide d (pm_fn (pr_map r) x))
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

(** The polynomial-time class is closed backwards under polynomial reductions. *)
Theorem inPFor_of_reduction {A B : Type} {sa : A -> nat} {sb : B -> nat}
  {L : A -> Prop} {M : B -> Prop}
  (r : PolyReductionFor sa sb L M) : InPFor sb M -> InPFor sa L.
Proof. intros [d]. exact (inhabits (pullback r d)). Qed.

Definition ClosedUnderReductionsFor {A : Type} (sa : A -> nat)
  (C : (A -> Prop) -> Prop) : Prop :=
  forall L M, inhabited (PolyReductionFor sa sa L M) -> C M -> C L.

Theorem inPFor_closed {A : Type} (sa : A -> nat) : ClosedUnderReductionsFor sa (InPFor sa).
Proof. intros L M [r] hM. exact (inPFor_of_reduction r hM). Qed.

(** A closed class containing a complete language contains the whole family. *)
Theorem closed_contains_family_for {A : Type} (sa : A -> nat) (C : (A -> Prop) -> Prop)
  (hC : ClosedUnderReductionsFor sa C) (family : (A -> Prop) -> Prop) (K : A -> Prop)
  (hard : forall L, family L -> inhabited (PolyReductionFor sa sa L K)) (hK : C K) :
  forall L, family L -> C L.
Proof. intros L hL. exact (hC L K (hard L hL) hK). Qed.

(** Schema: "reduce [L] to a language in [InPFor]", over declared costs. *)
Definition ReducesToPFor {A : Type} (sa : A -> nat) (L : A -> Prop) : Prop :=
  exists (B : Type) (sb : B -> nat) (M : B -> Prop),
    inhabited (PolyReductionFor sa sb L M) /\ InPFor sb M.

(** The obligation is exactly as hard as the goal. *)
Theorem reducesToPFor_iff_inPFor {A : Type} (sa : A -> nat) (L : A -> Prop) :
  ReducesToPFor sa L <-> InPFor sa L.
Proof.
  split.
  - intros [B [sb [M [[r] hM]]]]. exact (inPFor_of_reduction r hM).
  - intro h. exists A, sa, L. split; [| exact h].
    exact (inhabits (mkPolyReductionFor (polymap_ident sa) (reduction_id L))).
Qed.


(** The schema alone is vacuous: with declared cost [0], every decidable
    language is in [InPFor].  (Lean uses classical decidability of an
    arbitrary [L]; here the decision procedure is a premise.) *)
Theorem inPFor_every {A : Type} (sa : A -> nat) (L : A -> Prop)
  (dec : forall x, {L x} + {~ L x}) : InPFor sa L.
Proof.
  constructor.
  refine (mkPolyDeciderFor (fun x => if dec x then true else false) (fun _ => 0)
    poly_zero _ _).
  - intro x. destruct (dec x) as [h | h]; split; intro H.
    + reflexivity.
    + exact h.
    + contradiction.
    + discriminate.
  - intro x. lia.
Qed.

(** The number of steps a machine takes from [c] until it halts, computed with
    at most [fuel] steps. *)
Fixpoint stepCount (m : Machine) (c : Config) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' => match step m c with
               | inl _ => 1
               | inr c' => S (stepCount m c' fuel')
               end
  end.

(** With enough fuel, [stepCount] is the length of the run. *)
Theorem stepCount_of_run : forall m c t b, Run m c t b ->
  forall fuel, t <= fuel -> stepCount m c fuel = t.
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs _ IH]; intros fuel hf.
  - destruct fuel as [| fuel]; [lia |]. simpl. rewrite hs. reflexivity.
  - destruct fuel as [| fuel]; [lia |]. simpl. rewrite hs. f_equal. apply IH. lia.
Qed.

(** Instantiating the schema with the machine model: the step count of a
    polynomial-time machine is a declared cost bounded by the machine's
    polynomial.  (Lean picks the step count with [Classical.choose]; here it
    is computed by [stepCount].) *)
Theorem inPFor_of_inP (L : Language) (h : InP L) :
  InPFor (@length bool) (fun x => L x = true).
Proof.
  apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  constructor.
  refine (mkPolyDeciderFor L (fun x => stepCount m (initial x) (evalPoly p (length x)))
    (mkPoly (coefficient p) (degree p)) _ _).
  - intro x. reflexivity.
  - intro x. destruct (hm x) as [t [b [ht [hr _]]]].
    rewrite (stepCount_of_run _ _ _ _ hr _ ht). exact ht.
Qed.

(** * Reduction chains in the machine model *)

(** ** Composition of machine reductions

    [PolyReduces] is a preorder.  The composite reduction runs the table of
    the first machine and then the shifted table of the second
    ([appendMachine]); the second phase starts from the first machine's output
    tape, which agrees with the second machine's initial configuration up to
    trailing blanks. *)

Theorem reaches_trans : forall M c d e t1 t2,
  Reaches M c t1 d -> Reaches M d t2 e -> Reaches M c (t1 + t2) e.
Proof.
  intros M c d e t1 t2 h1 h2. induction h1 as [c | c c' d t hs _ IH].
  - exact h2.
  - simpl. apply reaches_next with c'; auto.
Qed.

(** A partial run of the second table is a partial run of the concatenation,
    with every state shifted by the length of the first table. *)
Theorem reaches_append_right : forall first second c d t,
  Reaches second c t d ->
  Reaches (appendMachine first second) (shiftConfig (length (program first)) c) t
    (shiftConfig (length (program first)) d).
Proof.
  intros first second c d t h. induction h as [c | c c' d t hs _ IH].
  - apply reaches_refl.
  - apply reaches_next with (shiftConfig (length (program first)) c'); [| exact IH].
    unfold step in hs |- *.
    change (state (shiftConfig (length (program first)) c))
      with (state c + length (program first)).
    change (tapeHead (shiftConfig (length (program first)) c)) with (tapeHead c).
    rewrite append_instruction_right.
    destruct (instruction second (state c) (tapeHead c)) as [b' | q w dir];
      [discriminate |].
    injection hs as <-. simpl. rewrite moveHead_shift. reflexivity.
Qed.

(** Partial runs ignore trailing blanks. *)
Theorem reaches_of_similar : forall M c d c' t,
  Reaches M c t d -> Similar c c' -> exists d', Reaches M c' t d' /\ Similar d d'.
Proof.
  intros M c d c' t h. revert c'.
  induction h as [c | c c1 d t hs _ IH]; intros c' hsim.
  - exists c'. split; [apply reaches_refl | exact hsim].
  - destruct (proj2 (similar_step M c c' hsim) c1 hs) as [e' [he' hsim']].
    destruct (IH e' hsim') as [d' [hd' hsd]].
    exists d'. split; [apply reaches_next with e'; auto | exact hsd].
Qed.

Theorem blankPad_blanks : forall l s, BlankPad (blanks l) s -> exists l', s = blanks l'.
Proof.
  induction l as [| l IH]; intros s h.
  - induction s as [| b s IHs].
    + exists 0. reflexivity.
    + destruct (blankPad_nil_cons b s h) as [hb hs].
      destruct (IHs hs) as [l' hl']. exists (S l'). subst. reflexivity.
  - destruct s as [| b s].
    + exists 0. reflexivity.
    + destruct (blankPad_cons_cons blank b (blanks l) s h) as [hb hs].
      destruct (IH s hs) as [l' hl']. exists (S l'). subst. reflexivity.
Qed.

(** A tape holding a word followed by blanks keeps that form under
    [BlankPad]. *)
Theorem blankPad_word : forall (w : Word) l s,
  BlankPad (map ofBool w ++ blanks l) s -> exists l', s = map ofBool w ++ blanks l'.
Proof.
  induction w as [| a w IH]; intros l s h.
  - exact (blankPad_blanks l s h).
  - destruct s as [| b s].
    + destruct (blankPad_nil_cons _ _ (blankPad_symm _ _ h)) as [ha _].
      destruct a; discriminate.
    + destruct (blankPad_cons_cons _ _ _ _ h) as [hab hs].
      destruct (IH l s hs) as [l' hl']. exists l'. subst. reflexivity.
Qed.

Theorem appendMachine_length : forall first second,
  length (program (appendMachine first second)) =
    length (program first) + length (program second).
Proof.
  intros first second. unfold appendMachine. simpl.
  rewrite length_app, length_map. reflexivity.
Qed.

(** The empty table computes the identity in zero steps. *)
Theorem computes_id :
  Computes {| program := [] |} (fun x => x) {| coefficient := 0; degree := 0 |}.
Proof.
  intro x. exists 0, (initial x). split; [lia |]. split; [apply reaches_refl |].
  destruct x as [| a x].
  - split; [reflexivity | split; [reflexivity |]]. exists 1. reflexivity.
  - split; [reflexivity | split; [reflexivity |]]. exists 0. simpl.
    rewrite app_nil_r. reflexivity.
Qed.

(** Composition of computed maps (machine construction). *)
Theorem computes_comp : forall m m' f g p p',
  Computes m f p -> Computes m' g p' ->
  exists B : Polynomial, Computes (appendMachine m m') (fun x => g (f x)) B.
Proof.
  intros m m' f g p p' hm hm'.
  destruct (computes_output_poly m f p hm) as [q hq].
  destruct (compose_bound p p' q) as [B hB].
  exists B. intro x.
  destruct (hm x) as [t1 [c [ht1 [hr1 [hs1 [hl1 [k htape1]]]]]]].
  destruct (hm' (f x)) as [t2 [d [ht2 [hr2 [hs2 [hl2 [k2 htape2]]]]]]].
  pose proof (similar_initial (f x) c (length (program m)) hs1 hl1 k htape1) as hsim.
  destruct (reaches_of_similar _ _ _ _ _ (reaches_append_right m m' _ _ _ hr2) hsim)
    as [d' [hr2' hsd]].
  destruct hsd as [hst [hle [hhd hpad]]].
  cbn [shiftConfig state tapeLeft tapeHead tapeRight] in hst, hle, hhd, hpad.
  pose proof (blankPad_cons _ _ (tapeHead d) hpad) as hpad'.
  rewrite htape2 in hpad'.
  destruct (blankPad_word _ _ _ hpad') as [l' hl'].
  exists (t1 + t2), d'. split.
  { pose proof (polynomial_eval_mono p' _ _ (hq x)). pose proof (hB (length x)). lia. }
  split; [apply reaches_trans with c; [apply reaches_append; exact hr1 | exact hr2'] |].
  split; [rewrite appendMachine_length, <- hst, hs2; lia |].
  split; [rewrite <- hle; exact hl2 |].
  exists l'. rewrite <- hhd. exact hl'.
Qed.

(** [PolyReduces] is reflexive. *)
Theorem polyReduces_refl : forall L, PolyReduces L L.
Proof.
  intro L. exists {| program := [] |}, (fun x => x), {| coefficient := 0; degree := 0 |}.
  split; [exact computes_id | reflexivity].
Qed.

(** [PolyReduces] is transitive: machine reductions compose. *)
Theorem polyReduces_trans : forall L M N, PolyReduces L M -> PolyReduces M N -> PolyReduces L N.
Proof.
  intros L M N [m [f [p [hm hf]]]] [m' [g [p' [hm' hg]]]].
  destruct (computes_comp m m' f g p p' hm hm') as [B hB].
  exists (appendMachine m m'), (fun x => g (f x)), B. split; [exact hB |].
  intro x. rewrite hf. apply hg.
Qed.

(** Membership in P is inherited backwards along a two-step chain. *)
Theorem inP_of_chain : forall L M N,
  PolyReduces L M -> PolyReduces M N -> InP N -> InP L.
Proof.
  intros L M N h1 h2 hN. exact (inP_of_reduces L N (polyReduces_trans L M N h1 h2) hN).
Qed.

(** A class of languages closed backwards under machine reductions. *)
Definition ClosedUnderPolyReduces (C : Language -> Prop) : Prop :=
  forall L M, PolyReduces L M -> C M -> C L.

(** [InP] is closed under machine reductions. *)
Theorem inP_closedUnderPolyReduces : ClosedUnderPolyReduces InP.
Proof. intros L M hr hM. exact (inP_of_reduces L M hr hM). Qed.

(** NP-hardness is inherited forwards along machine reductions. *)
Theorem npHard_of_reduces : forall K M, NPHard K -> PolyReduces K M -> NPHard M.
Proof. intros K M hK hr L hL. exact (polyReduces_trans L K M (hK L hL) hr). Qed.

(** Any class closed under machine reductions that contains an NP-hard
    language contains all of NP. *)
Theorem closed_contains_np : forall (C : Language -> Prop), ClosedUnderPolyReduces C ->
  forall K, NPHard K -> C K -> forall L, InNP L -> C L.
Proof. intros C hC K hK hCK L hL. exact (hC L K (hK L hL) hCK). Qed.

(** An NP-hard language in P gives P = NP. *)
Theorem pEqualsNP_of_npHard_inP : forall K, NPHard K -> InP K -> PEqualsNP.
Proof.
  intros K hK hP. exact (closed_contains_np InP inP_closedUnderPolyReduces K hK hP).
Qed.

(** "Reduce [L] to a language already in P", in the machine model. *)
Definition ReducesToP (L : Language) : Prop := exists L' : Language, PolyReduces L L' /\ InP L'.

(** Reducing [L] to some language in P is equivalent to [L] in P. *)
Theorem reducesToP_iff_inP : forall L, ReducesToP L <-> InP L.
Proof.
  intro L. split.
  - intros [L' [hr hL']]. exact (inP_of_reduces L L' hr hL').
  - intro h. exists L. split; [apply polyReduces_refl | exact h].
Qed.

(** Non-vacuity: not every language reduces to a language in P (the shared
    diagonal language [Diag] does not). *)
Theorem not_forall_reducesToP : ~ (forall L : Language, ReducesToP L).
Proof. intro h. exact (diag_not_inP (proj1 (reducesToP_iff_inP Diag) (h Diag))). Qed.

(** * The obligation of the "reduce SAT to P" route *)

(** Open obligation: a machine reduction ([PolyReduces]) from [SAT] to some
    language [L'] together with a polynomial-time machine for [L'].  This is
    the obligation of every "reduce NP to an easy problem" argument, stated in
    the shared machine model; it is a definition and is never postulated. *)
Definition SATReducesToP : Prop := exists L' : Language, PolyReduces SAT L' /\ InP L'.

(** The obligation is exactly as hard as the goal: it is equivalent to
    [InP SAT]. *)
Theorem satReducesToP_iff_inP_sat : SATReducesToP <-> InP SAT.
Proof. exact (reducesToP_iff_inP SAT). Qed.

(** Conditional theorem: under the named premise [SATHard] (hardness half of
    Cook-Levin, not mechanised here) the obligation gives P = NP. *)
Theorem pEqualsNP_of_satReducesToP : SATHard -> SATReducesToP -> PEqualsNP.
Proof.
  intros hard h. exact (pEqualsNP_of_inP_sat hard (proj1 satReducesToP_iff_inP_sat h)).
Qed.

(** Under the named premise [CookLevin] the obligation is exactly P = NP. *)
Theorem satReducesToP_iff_pEqualsNP : CookLevin -> (SATReducesToP <-> PEqualsNP).
Proof.
  intro hCL. rewrite satReducesToP_iff_inP_sat. exact (inP_sat_iff hCL).
Qed.

(** Refuting the obligation would separate P from NP (given [SATInNP]). *)
Theorem pNotEqualsNP_of_not_satReducesToP : SATInNP -> ~ SATReducesToP -> PNotEqualsNP.
Proof.
  intros mem h hp. apply h. apply satReducesToP_iff_inP_sat.
  exact (inP_sat_of_pEqualsNP mem hp).
Qed.

(** A chain [SAT -> L1 -> L2] ending in P discharges the obligation. *)
Theorem satReducesToP_of_chain : forall L1 L2,
  PolyReduces SAT L1 -> PolyReduces L1 L2 -> InP L2 -> SATReducesToP.
Proof.
  intros L1 L2 h1 h2 hP. exists L2. split; [exact (polyReduces_trans SAT L1 L2 h1 h2) | exact hP].
Qed.
