(** * Issue #532, Idea 12: reduction verification

    Rocq counterpart of [lean/Idea12.lean]; theorem names are aligned.

    Many-one reductions [f : A -> B] from [L : A -> bool] to [M : B -> bool]
    ([IsReduction f L M := forall x, L x = M (f x)]), first without resources
    and then in the shared machine model [Machines.v], where a reduction is
    [PolyReduces L L']: a finite-table machine computes the map within a
    polynomial number of [Run] steps ([Computes m f p]).

    Proved for all types, languages and maps (no cost): [reduction_id],
    [reduction_comp], [reduction_complement], [const_reduction_iff],
    [const_not_reduction], [trivial_target], [nontrivial_target],
    [decider_transfer], [yes_preserving_not_sufficient],
    [reduces_to_any_nontrivial].

    Proved in the machine model:
    - [polyReduces_refl], [polyReduces_trans] (via [computes_comp]): machine
      reductions form a preorder; the composite machine is the concatenated
      table [appendMachine m m'];
    - [polyReduces_complement];
    - [poly_decider_transfer] (the shared [inP_of_reduces]),
      [hardness_transfer], [sat_hardness_transfer], [diag_hardness_transfer];
    - [reduction_cost_essential]: [Diag] reduces to the nontrivial language
      [firstBit] by an unrestricted map, but not by any [PolyReduces];
    - [sat_reduction_route_iff], [pEqualsNP_of_sat_reduction_route],
      [npHard_of_reduces].

    The earlier abstract cost model (an [Algo] with a declared [time] field)
    is kept as a schema: [Algo], [PolyBoundedFor], [PolyDeciderFor],
    [PolyReductionFor] and the theorems with suffix [_for].
    [polyDeciderFor_every] shows the schema alone is vacuous, and
    [polyDeciderFor_of_inP] instantiates it with the machine step count
    ([stepCount], computed by a fuelled interpreter, so no choice principle is
    needed).  No axioms are used.

    Verdict: correct tool, insufficient alone.  Nothing here proves or
    refutes P = NP. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** [f] is a many-one reduction from [L] to [M]. *)
Definition IsReduction {A B : Type} (f : A -> B) (L : A -> bool) (M : B -> bool) : Prop :=
  forall x, L x = M (f x).

(** [L] has a yes-instance and a no-instance. *)
Definition Nontrivial {T : Type} (L : T -> bool) : Prop :=
  exists a b, L a = true /\ L b = false.

Theorem reduction_id : forall {A : Type} (L : A -> bool), IsReduction id L L.
Proof. intros A L x. reflexivity. Qed.

(** Reductions compose. *)
Theorem reduction_comp : forall {A B C : Type} (f : A -> B) (g : B -> C) L M N,
  IsReduction f L M -> IsReduction g M N -> IsReduction (fun x => g (f x)) L N.
Proof. intros A B C f g L M N hf hg x. rewrite hf. apply hg. Qed.

Section Reductions.
Context {A B : Type}.

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

(** * Abstract cost schema

    A schema, not a statement about the machine model: the running time is a
    declared field of [Algo], so nothing ties it to an actual computation.
    [polyDeciderFor_every] makes this explicit. *)

Record Algo (A B : Type) := mkAlgo { run : A -> B; time : A -> nat }.
Arguments mkAlgo {A B} _ _.
Arguments run {A B} _ _.
Arguments time {A B} _ _.

(** Schema: [t] is bounded by [c * (sz x + 1)^d]. *)
Definition PolyBoundedFor {A : Type} (sz : A -> nat) (t : A -> nat) : Prop :=
  exists c d, forall x, t x <= c * (sz x + 1) ^ d.

(** Schema: [L] has an [Algo] with polynomially bounded declared time. *)
Definition PolyDeciderFor {A : Type} (sz : A -> nat) (L : A -> bool) : Prop :=
  exists D : Algo A bool, (forall x, run D x = L x) /\ PolyBoundedFor sz (time D).

(** Schema: a correct reduction [Algo] with polynomially bounded declared time
    and polynomial output size. *)
Definition PolyReductionFor {A B : Type} (szA : A -> nat) (szB : B -> nat)
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

(** Schema version of the transfer: deciders pull back along reductions,
    with explicit constants for the composed declared time. *)
Theorem poly_decider_transfer_for : forall {A B : Type} (szA : A -> nat) (szB : B -> nat) L M
  (R : Algo A B), PolyReductionFor szA szB L M R -> PolyDeciderFor szB M -> PolyDeciderFor szA L.
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

(** Schema version of composition (with explicit constants). *)
Theorem poly_reduction_comp_for : forall {A B C : Type} (szA : A -> nat) (szB : B -> nat)
  (szC : C -> nat) L M N (R : Algo A B) (S : Algo B C),
  PolyReductionFor szA szB L M R -> PolyReductionFor szB szC M N S ->
  PolyReductionFor szA szC L N (mkAlgo (fun x => run S (run R x)) (fun x => time R x + time S (run R x))).
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

(** Schema version of hardness transfer. *)
Theorem hardness_transfer_for : forall {A B : Type} (szA : A -> nat) (szB : B -> nat) L M
  (R : Algo A B), PolyReductionFor szA szB L M R -> ~ PolyDeciderFor szA L -> ~ PolyDeciderFor szB M.
Proof.
  intros A B szA szB L M R hR hL hM. apply hL. exact (poly_decider_transfer_for szA szB L M R hR hM).
Qed.


(** The schema alone is vacuous: with declared time [0], every language has a
    "polynomial decider".  Hence the premise [~ PolyDeciderFor szA L] of
    [hardness_transfer_for] is never satisfiable, and the schema must be
    instantiated with a real cost model. *)
Theorem polyDeciderFor_every : forall {A : Type} (sz : A -> nat) (L : A -> bool),
  PolyDeciderFor sz L.
Proof.
  intros A sz L. exists (mkAlgo L (fun _ => 0)). split; [reflexivity |].
  exists 0, 0. intro x. simpl. lia.
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
    polynomial-time machine is a polynomially bounded time function.  (Lean
    picks the step count with [Classical.choose]; here it is computed by
    [stepCount].) *)
Theorem polyDeciderFor_of_inP : forall L : Language, InP L -> PolyDeciderFor (@length bool) L.
Proof.
  intros L h. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  exists (mkAlgo L (fun x => stepCount m (initial x) (evalPoly p (length x)))).
  split; [reflexivity |].
  exists (coefficient p), (degree p). intro x. simpl.
  destruct (hm x) as [t [b [ht [hr _]]]].
  rewrite (stepCount_of_run _ _ _ _ hr _ ht). exact ht.
Qed.

(** * Reductions in the machine model *)

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

(** Machine reductions commute with complement (the same machine works). *)
Theorem polyReduces_complement : forall L L',
  PolyReduces L L' -> PolyReduces (complement L) (complement L').
Proof.
  intros L L' [m [f [p [hm hf]]]]. exists m, f, p. split; [exact hm |].
  intro x. unfold complement. rewrite hf. reflexivity.
Qed.

(** Polynomial deciders pull back along machine reductions (the shared
    [inP_of_reduces], the machine form of the transfer). *)
Theorem poly_decider_transfer : forall L L', PolyReduces L L' -> InP L' -> InP L.
Proof. exact inP_of_reduces. Qed.

(** Hardness transfers forward along machine reductions. *)
Theorem hardness_transfer : forall L L', PolyReduces L L' -> ~ InP L -> ~ InP L'.
Proof. intros L L' hr hL h. exact (hL (poly_decider_transfer L L' hr h)). Qed.

(** SAT instance: if [SAT] is not in P, nothing that [SAT] reduces to is in P. *)
Theorem sat_hardness_transfer : forall L', PolyReduces SAT L' -> ~ InP SAT -> ~ InP L'.
Proof. intros L'. apply hardness_transfer. Qed.

(** The premise of [hardness_transfer] is satisfiable: every target of a
    machine reduction from the diagonal language is outside P. *)
Theorem diag_hardness_transfer : forall L', PolyReduces Diag L' -> ~ InP L'.
Proof. intros L' hr. exact (hardness_transfer Diag L' hr diag_not_inP). Qed.

(** A nontrivial language in P: "the first bit is [1]". *)
Definition firstBit : Language := fun w =>
  match w with
  | true :: _ => true
  | _ => false
  end.

(** One row, one step: the machine answers by the scanned symbol. *)
Definition firstBitMachine : Machine :=
  {| program := [[halt false; halt false; halt true; halt false]] |}.

Theorem firstBit_inP : InP firstBit.
Proof.
  apply (inP_of_decidesWithin firstBitMachine {| coefficient := 1; degree := 0 |}).
  intro x. exists 1, (firstBit x). split; [unfold evalPoly; simpl; lia |].
  split; [| reflexivity].
  apply run_halt. destruct x as [| [|] x]; reflexivity.
Qed.

Theorem firstBit_nontrivial : Nontrivial firstBit.
Proof. exists [true], []. split; reflexivity. Qed.

(** The cost bound is essential.  [Diag] reduces to the nontrivial language
    [firstBit] by an unrestricted map ([reduces_to_any_nontrivial]), but by no
    machine reduction, since [firstBit] is in P and [Diag] is not. *)
Theorem reduction_cost_essential :
  (exists f : Word -> Word, IsReduction f Diag firstBit) /\ ~ PolyReduces Diag firstBit.
Proof.
  split.
  - exact (reduces_to_any_nontrivial Diag firstBit firstBit_nontrivial).
  - intro hr. exact (diag_hardness_transfer firstBit hr firstBit_inP).
Qed.

(** "Reduce SAT to something in P" is exactly [InP SAT]: reductions only move
    the question. *)
Theorem sat_reduction_route_iff : (exists M : Language, PolyReduces SAT M /\ InP M) <-> InP SAT.
Proof.
  split.
  - intros [M [hr hM]]. exact (inP_of_reduces SAT M hr hM).
  - intro h. exists SAT. split; [apply polyReduces_refl | exact h].
Qed.

(** Conditional theorem: the route gives P = NP under the named premise
    [SATHard] (the hardness half of Cook-Levin, not mechanised here). *)
Theorem pEqualsNP_of_sat_reduction_route : SATHard ->
  (exists M : Language, PolyReduces SAT M /\ InP M) -> PEqualsNP.
Proof.
  intros hard h. exact (pEqualsNP_of_inP_sat hard (proj1 sat_reduction_route_iff h)).
Qed.

(** Hardness of [SAT] pushed forward: if [SAT] is NP-hard in the machine
    sense and [SAT] reduces to [M], then [M] is NP-hard. *)
Theorem npHard_of_reduces : forall M, SATHard -> PolyReduces SAT M -> NPHard M.
Proof.
  intros M hard hr L hL. exact (polyReduces_trans L SAT M (hard L hL) hr).
Qed.
