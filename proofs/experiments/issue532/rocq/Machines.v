(** * Issue #532: machine-level infrastructure shared by the idea files

    Rocq twin of [proofs/experiments/issue532/lean/Machines.lean]; theorem
    names are aligned (Lean dotted names such as [Reaches.run] or
    [BlankPad.refl] become [reaches_run], [blankPad_refl], ...).

    Every cost statement in the idea files that concerns P versus NP is stated
    over the repository's single machine model
    [proofs/complexity/rocq/Complexity.v]: a decider is a [Machine] and its
    time is the step count [t] of a [Run].  This file re-exports that model
    and supplies the general facts the idea files need.

    - [run_deterministic]: a machine has at most one run from a configuration.
    - [PolyDec], [polyDec_iff_inP]: a polynomial-time machine decider, and its
      equivalence with [InP].
    - [Reaches], [Computes], [PolyReduces]: function-computing machines and
      polynomial-time many-one reductions.
    - [computes_output_length]: a machine's output is at most as long as its
      input plus its running time plus one, so reductions need no separate
      size bound.
    - [compose_run], [inP_of_promise_reduction], [inP_of_reduces]: running a
      function machine and then a decider is a run of one composed table (the
      reducer's table followed by the decider's table with shifted state
      numbers).  P is closed under reductions, and a machine map into a
      promise composed with a machine that is correct only on the promise
      decides the whole language.
    - [flipMachine], [inP_complement], [npEqualsCoNP_of_pEqualsNP]: P is closed
      under complement, so P = NP implies NP = coNP.
    - [NPHard], [NPComplete], [npComplete_inP_iff]: an NP-complete language is
      in P if and only if P = NP.
    - [encMachine_injective], [diag_not_inP], [exists_not_inP],
      [exists_language_not_in_family]: an injective encoding of machines as
      words (with a computable decoder), a diagonal language outside P, and a
      Cantor lemma, so statements of the form [InP L] are not provable for
      every [L].
    - [CNF], [bruteForce_correct], [encodeCNF], [decode_encode], [SAT],
      [sat_iff]: CNF formulas, the brute-force decider, a lossless binary
      encoding with a total parser, and SAT as a computable [Language].
    - [SATInNP], [SATHard], [CookLevin], [inP_sat_iff]: the Cook-Levin theorem
      stated in this model, and "SAT in P <-> P = NP" under it.  The
      membership half [SATInNP] is proved in [SATVerifier.v] ([satInNP])
      with an explicit verifier machine.  The hardness half [SATHard] is a
      known theorem that is NOT proved here; every use is an explicit
      hypothesis named [SATHard] or [CookLevin].

    Differences from the Lean file (Rocq has no function extensionality and no
    classical logic here; this file uses no axioms at all):
    - [computes_unique] and [complement_complement] are stated pointwise
      ([forall x, f x = g x]) instead of as equalities of functions; [inP_ext]
      transports [InP] along pointwise equality.
    - [Diag] is not the Lean diagonal (which is [noncomputable] and decides
      "the machine coded by [w] accepts [w] in some number of steps" with
      [Classical]).  Here [Diag] diagonalises against (machine, polynomial)
      pairs with the step-bounded interpreter [runFor]: [w] is in [Diag] unless
      [w] decodes (via [decMachinePoly]) to a pair [(m, p)] such that [m]
      accepts [w] within [p(|w|)] steps.  [Diag] is computable and the
      exported statements [diag_not_inP], [exists_not_inP],
      [not_forall_polyDec] are the same as in Lean.
    - [exists_language_not_in_family] takes a left inverse
      [d : Word -> option T] of the encoding ([d (e a) = Some a]) instead of
      mere injectivity (a left inverse implies injectivity; with injectivity
      alone the diagonal is not constructively definable).  The encodings
      [encMachine] and [encMachinePoly] come with such decoders
      ([decMachine_encMachine], [decMachinePoly_encMachinePoly]). *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.complexity.rocq Require Export Complexity.
Export Complexity.Complexity.

(** ** Determinism *)

(** A machine has at most one run from a configuration. *)
Theorem run_deterministic : forall m c t t' b b',
  Run m c t b -> Run m c t' b' -> t = t' /\ b = b'.
Proof.
  intros m c t t' b b' h. revert t' b'.
  induction h as [c b hs | c c' t b hs hr IH]; intros t' b' h'.
  - inversion h' as [c0 b0 hs' | c0 c0' t0 b0 hs' hr']; subst;
      rewrite hs in hs'; inversion hs'; auto.
  - inversion h' as [c0 b0 hs' | c0 c0' t0 b0 hs' hr']; subst;
      rewrite hs in hs'; inversion hs'; subst.
    destruct (IH _ _ hr') as [h1 h2]. split; [lia | exact h2].
Qed.

(** ** Polynomial-time machine deciders *)

(** [m] decides [L] within the polynomial [p]: on every input it halts within
    [p(|x|)] steps with the answer [L x]. *)
Definition DecidesWithin (m : Machine) (p : Polynomial) (L : Language) : Prop :=
  forall x, exists t b, t <= evalPoly p (length x) /\ Run m (initial x) t b /\ b = L x.

(** A polynomial-time machine decider: the decider is a [Machine] and the time
    is the step count of [Run]. *)
Definition PolyDec (L : Language) : Prop :=
  exists (m : Machine) (p : Polynomial), DecidesWithin m p L.

Definition classP_of_decidesWithin (m : Machine) (p : Polynomial) (L : Language)
    (h : DecidesWithin m p L) : ClassP.
Proof.
  refine {| p_language := L; p_machine := m; p_bound := p |}.
  - intro x. destruct (h x) as [t [b [ht [hr _]]]]. exists t, b. auto.
  - intros x t b hr. destruct (h x) as [t' [b' [_ [hr' hb']]]].
    destruct (run_deterministic _ _ _ _ _ _ hr hr') as [_ ->]. subst b'.
    split; auto.
Defined.

Theorem inP_of_decidesWithin : forall m p L, DecidesWithin m p L -> InP L.
Proof.
  intros m p L h. exists (classP_of_decidesWithin m p L h). reflexivity.
Qed.

Theorem decidesWithin_of_classP : forall P : ClassP,
  DecidesWithin (p_machine P) (p_bound P) (p_language P).
Proof.
  intros P x. destruct (p_terminates P x) as [t [b [ht hr]]].
  exists t, b. split; [exact ht | split; [exact hr |]].
  pose proof (p_correct P x t b hr) as hc.
  destruct b, (p_language P x); auto; destruct hc as [h1 h2].
  - discriminate (h2 eq_refl).
  - discriminate (h1 eq_refl).
Qed.

(** [PolyDec] is exactly membership in the repository's class P. *)
Theorem polyDec_iff_inP : forall L, PolyDec L <-> InP L.
Proof.
  intro L. split.
  - intros [m [p h]]. exact (inP_of_decidesWithin m p L h).
  - intros [P hP]. subst L. exists (p_machine P), (p_bound P).
    apply decidesWithin_of_classP.
Qed.

(** [InP] only depends on the values of the language (no function
    extensionality is needed). *)
Theorem inP_ext : forall L L', (forall x, L x = L' x) -> InP L -> InP L'.
Proof.
  intros L L' hLL' hL. apply polyDec_iff_inP in hL. destruct hL as [m [p h]].
  apply (inP_of_decidesWithin m p). intro x.
  destruct (h x) as [t [b [ht [hr hb]]]]. exists t, b. rewrite <- hLL'. auto.
Qed.

(** ** Partial runs *)

(** [Reaches m c t d]: [t] non-halting steps lead from [c] to [d]. *)
Inductive Reaches (m : Machine) : Config -> nat -> Config -> Prop :=
| reaches_refl : forall c, Reaches m c 0 c
| reaches_next : forall c c' d t,
    step m c = inr c' -> Reaches m c' t d -> Reaches m c (S t) d.

Theorem reaches_run : forall m c d t t' b,
  Reaches m c t d -> Run m d t' b -> Run m c (t + t') b.
Proof.
  intros m c d t t' b h hr. induction h as [c | c c' d t hs _ IH].
  - exact hr.
  - simpl. apply run_next with c'; auto.
Qed.

(** ** Tapes that differ only by trailing blanks *)

Definition blanks (k : nat) : list Symbol := repeat blank k.

(** [r] and [s] agree up to trailing blanks. *)
Definition BlankPad (r s : list Symbol) : Prop :=
  exists u k l, r = u ++ blanks k /\ s = u ++ blanks l.

Theorem blankPad_refl : forall r, BlankPad r r.
Proof. intro r. exists r, 0, 0. simpl. rewrite app_nil_r. auto. Qed.

Theorem blankPad_symm : forall r s, BlankPad r s -> BlankPad s r.
Proof. intros r s [u [k [l [hr hs]]]]. exists u, l, k. auto. Qed.

Theorem blankPad_cons : forall r s a, BlankPad r s -> BlankPad (a :: r) (a :: s).
Proof.
  intros r s a [u [k [l [hr hs]]]]. exists (a :: u), k, l. subst. auto.
Qed.

Theorem blankPad_cons_cons : forall a b r s,
  BlankPad (a :: r) (b :: s) -> a = b /\ BlankPad r s.
Proof.
  intros a b r s [u [k [l [hr hs]]]]. destruct u as [| x u].
  - destruct k as [| k]; [discriminate |]. destruct l as [| l]; [discriminate |].
    simpl in hr, hs. injection hr as -> ->. injection hs as -> ->.
    split; [reflexivity |]. exists [], k, l. auto.
  - simpl in hr, hs. injection hr as -> ->. injection hs as -> ->.
    split; [reflexivity |]. exists u, k, l. auto.
Qed.

Theorem blankPad_nil_cons : forall b s,
  BlankPad [] (b :: s) -> b = blank /\ BlankPad [] s.
Proof.
  intros b s [u [k [l [hr hs]]]]. destruct u as [| x u].
  - destruct l as [| l]; [discriminate |]. simpl in hs. injection hs as -> ->.
    split; [reflexivity |]. exists [], 0, l. auto.
  - discriminate.
Qed.

(** Configurations that differ only by trailing blanks on the right. *)
Definition Similar (c d : Config) : Prop :=
  state c = state d /\ tapeLeft c = tapeLeft d /\ tapeHead c = tapeHead d /\
  BlankPad (tapeRight c) (tapeRight d).

Theorem similar_symm : forall c d, Similar c d -> Similar d c.
Proof.
  intros c d [h1 [h2 [h3 h4]]]. split; [auto | split; [auto | split; [auto |]]].
  apply blankPad_symm; exact h4.
Qed.

Theorem similar_moveHead : forall c d, Similar c d -> forall q w dir,
  Similar (moveHead c q w dir) (moveHead d q w dir).
Proof.
  intros [cs cl ch cr] [ds dl dh dr] [_ [hl [_ hr]]] q w dir.
  simpl in hl, hr. subst dl. unfold Similar.
  destruct dir; simpl.
  - destruct cl as [| a rest]; simpl;
      (split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]);
      apply blankPad_cons; exact hr.
  - destruct cr as [| a r]; destruct dr as [| b s]; simpl;
      (split; [reflexivity | split; [reflexivity |]]).
    + split; [reflexivity | apply blankPad_refl].
    + destruct (blankPad_nil_cons _ _ hr) as [hb hs].
      split; [symmetry; exact hb | exact hs].
    + destruct (blankPad_nil_cons _ _ (blankPad_symm _ _ hr)) as [ha hs].
      split; [exact ha | apply blankPad_symm; exact hs].
    + destruct (blankPad_cons_cons _ _ _ _ hr) as [hab hs].
      split; [exact hab | exact hs].
  - split; [reflexivity | split; [reflexivity | split; [reflexivity | exact hr]]].
Qed.

Theorem similar_step : forall m c d, Similar c d ->
  (forall b, step m c = inl b -> step m d = inl b) /\
  (forall c', step m c = inr c' -> exists d', step m d = inr d' /\ Similar c' d').
Proof.
  intros m c d h. pose proof h as [hs [_ [hh _]]].
  unfold step. rewrite hs, hh.
  destruct (instruction m (state d) (tapeHead d)) as [b | q w dir].
  - split; auto. intros c' H. discriminate.
  - split; [intros b H; discriminate |].
    intros c' H. injection H as <-. eexists. split; [reflexivity |].
    apply similar_moveHead; exact h.
Qed.

(** Runs ignore trailing blanks. *)
Theorem run_of_similar : forall m c d t b, Run m c t b -> Similar c d -> Run m d t b.
Proof.
  intros m c d t b hr. revert d.
  induction hr as [c b hs | c c' t b hs _ IH]; intros d h.
  - apply run_halt. exact (proj1 (similar_step m c d h) b hs).
  - destruct (proj2 (similar_step m c d h) c' hs) as [d' [hd' hsim]].
    apply run_next with d'; auto.
Qed.

(** ** Instruction tables: missing rows, shifted tables and concatenation *)

Theorem instruction_of_length_le : forall m q a,
  length (program m) <= q -> instruction m q a = halt false.
Proof.
  intros m q a hq. unfold instruction.
  rewrite (proj2 (nth_error_None (program m) q) hq). reflexivity.
Qed.

(** A non-halting step starts in a state inside the table. *)
Theorem state_lt_of_step : forall m c c', step m c = inr c' ->
  state c < length (program m).
Proof.
  intros m c c' h. destruct (Nat.lt_ge_cases (state c) (length (program m)))
    as [hlt | hge]; [exact hlt |].
  unfold step in h. rewrite (instruction_of_length_le m _ (tapeHead c) hge) in h.
  discriminate.
Qed.

Definition shiftInstruction (off : nat) (i : Instruction) : Instruction :=
  match i with
  | halt b => halt b
  | move q w d => move (q + off) w d
  end.

(** The table of [first] followed by the table of [second] with every state
    number increased by [length (program first)]. *)
Definition appendMachine (first second : Machine) : Machine :=
  {| program := program first ++
       map (map (shiftInstruction (length (program first)))) (program second) |}.

Theorem append_instruction_left : forall first second q a,
  q < length (program first) ->
  instruction (appendMachine first second) q a = instruction first q a.
Proof.
  intros first second q a hq. unfold instruction, appendMachine. simpl.
  rewrite nth_error_app1 by exact hq. reflexivity.
Qed.

(** Lean's [Option.getD] is the match below. *)
Theorem getD_map_shift : forall off (o : option Instruction),
  match option_map (shiftInstruction off) o with Some i => i | None => halt false end =
    shiftInstruction off (match o with Some i => i | None => halt false end).
Proof. intros off [i |]; reflexivity. Qed.

Theorem append_instruction_right : forall first second q a,
  instruction (appendMachine first second) (q + length (program first)) a =
    shiftInstruction (length (program first)) (instruction second q a).
Proof.
  intros first second q a. unfold instruction, appendMachine. simpl.
  rewrite nth_error_app2 by lia. rewrite Nat.add_sub, nth_error_map.
  destruct (nth_error (program second) q) as [row |]; simpl; [| reflexivity].
  rewrite nth_error_map. apply getD_map_shift.
Qed.

Theorem reaches_append : forall first second c t d,
  Reaches first c t d -> Reaches (appendMachine first second) c t d.
Proof.
  intros first second c t d h. induction h as [c | c c' d t hs _ IH].
  - apply reaches_refl.
  - apply reaches_next with c'; [| exact IH].
    pose proof (state_lt_of_step _ _ _ hs) as hlt.
    unfold step in hs |- *. rewrite append_instruction_left by exact hlt.
    exact hs.
Qed.

Definition shiftConfig (off : nat) (c : Config) : Config :=
  {| state := state c + off; tapeLeft := tapeLeft c; tapeHead := tapeHead c;
     tapeRight := tapeRight c |}.

Theorem moveHead_shift : forall c off q w dir,
  moveHead (shiftConfig off c) (q + off) w dir = shiftConfig off (moveHead c q w dir).
Proof.
  intros [s l h r] off q w dir. destruct dir, l, r; reflexivity.
Qed.

Theorem run_append : forall first second c t b, Run second c t b ->
  Run (appendMachine first second) (shiftConfig (length (program first)) c) t b.
Proof.
  intros first second c t b h.
  induction h as [c b hs | c c' t b hs _ IH].
  - apply run_halt. unfold step in hs |- *.
    change (state (shiftConfig (length (program first)) c))
      with (state c + length (program first)).
    change (tapeHead (shiftConfig (length (program first)) c)) with (tapeHead c).
    rewrite append_instruction_right.
    destruct (instruction second (state c) (tapeHead c)); [exact hs | discriminate].
  - apply run_next with (shiftConfig (length (program first)) c'); [| exact IH].
    unfold step in hs |- *.
    change (state (shiftConfig (length (program first)) c))
      with (state c + length (program first)).
    change (tapeHead (shiftConfig (length (program first)) c)) with (tapeHead c).
    rewrite append_instruction_right.
    destruct (instruction second (state c) (tapeHead c)) as [b' | q w d];
      [discriminate |].
    injection hs as <-. simpl. rewrite moveHead_shift. reflexivity.
Qed.

(** ** Function-computing machines and reductions *)

(** [m] computes [f] within the polynomial [p]: from [initial x] it reaches,
    after at most [p(|x|)] steps, the state [length (program m)] just past its
    table, with the head on the leftmost cell and the tape holding [f x]
    followed by blanks. *)
Definition Computes (m : Machine) (f : Word -> Word) (p : Polynomial) : Prop :=
  forall x, exists t c, t <= evalPoly p (length x) /\ Reaches m (initial x) t c /\
    state c = length (program m) /\ tapeLeft c = [] /\
    exists k, tapeHead c :: tapeRight c = map ofBool (f x) ++ blanks k.

(** Polynomial-time many-one reduction in the machine model: a machine
    computes [f] in polynomial time and [L x = L' (f x)]. *)
Definition PolyReduces (L L' : Language) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial),
    Computes m f p /\ forall x, L x = L' (f x).

(** ** Tape size grows by at most one cell per step *)

Definition tapeSize (c : Config) : nat := length (tapeLeft c) + 1 + length (tapeRight c).

Theorem tapeSize_moveHead : forall c q w dir,
  tapeSize (moveHead c q w dir) <= tapeSize c + 1.
Proof.
  intros [s l h r] q w dir. unfold tapeSize.
  destruct dir, l, r; simpl; lia.
Qed.

Theorem tapeSize_reaches : forall m c d t, Reaches m c t d -> tapeSize d <= tapeSize c + t.
Proof.
  intros m c d t h. induction h as [c | c c' d t hs _ IH].
  - lia.
  - assert (tapeSize c' <= tapeSize c + 1).
    { unfold step in hs.
      destruct (instruction m (state c) (tapeHead c)) as [b | q w dir];
        [discriminate |].
      injection hs as <-. apply tapeSize_moveHead. }
    lia.
Qed.

Theorem tapeSize_initial : forall x, tapeSize (initial x) <= length x + 1.
Proof.
  intro x. unfold initial.
  assert (hlen : length (map ofBool x) = length x) by apply length_map.
  destruct (map ofBool x) as [| a rest]; unfold tapeSize; simpl in *; lia.
Qed.

(** The output of a machine is at most as long as its input plus its running
    time plus one. *)
Theorem computes_output_length : forall m f p, Computes m f p ->
  forall x, length (f x) <= length x + 1 + evalPoly p (length x).
Proof.
  intros m f p hm x.
  destruct (hm x) as [t [c [ht [hr [_ [hl [k htape]]]]]]].
  pose proof (tapeSize_reaches _ _ _ _ hr) as h1.
  pose proof (tapeSize_initial x) as h2.
  apply (f_equal (@length Symbol)) in htape.
  rewrite length_app, length_map in htape. simpl in htape.
  unfold tapeSize in h1 at 1. rewrite hl in h1. cbn [length] in h1. lia.
Qed.

Lemma polynomiallyBounded_evalPoly : forall p : Polynomial,
  PolynomiallyBounded (evalPoly p).
Proof. intro p. exists (coefficient p), (degree p). intro n. apply le_n. Qed.

(** The output length of a polynomial-time machine is polynomially bounded. *)
Theorem computes_output_poly : forall m f p, Computes m f p ->
  exists q : Polynomial, forall x, length (f x) <= evalPoly q (length x).
Proof.
  intros m f p hm.
  assert (hb : PolynomiallyBounded (fun n => n + 1 + evalPoly p n))
    by exact (polynomiallyBounded_add _ _ polynomiallyBounded_succ
                (polynomiallyBounded_evalPoly p)).
  destruct (proj1 (polynomiallyBounded_iff_polynomial _) hb) as [q hq].
  exists q. intro x. eapply Nat.le_trans; [apply (computes_output_length m f p hm x) |].
  apply hq.
Qed.

(** A partial run that ends in the exit state [length (program m)] is unique:
    no step is possible from the exit state. *)
Theorem reaches_exit_unique : forall m c d d' t t',
  Reaches m c t d -> Reaches m c t' d' ->
  state d = length (program m) -> state d' = length (program m) -> d = d'.
Proof.
  intros m c d d' t t' h. revert t' d'.
  induction h as [c | c c' d t hs hr IH]; intros t' d' h' hd hd'.
  - inversion h' as [c0 | c0 c0' d0 t0 hs' hr']; subst; [reflexivity |].
    pose proof (state_lt_of_step _ _ _ hs'). lia.
  - inversion h' as [c0 | c0 c0' d0 t0 hs' hr']; subst.
    + pose proof (state_lt_of_step _ _ _ hs). lia.
    + rewrite hs in hs'. injection hs' as <-. exact (IH _ _ hr' hd hd').
Qed.

Theorem map_ofBool_blanks_injective : forall u v k l,
  map ofBool u ++ blanks k = map ofBool v ++ blanks l -> u = v.
Proof.
  induction u as [| a u IH]; intros v k l h.
  - destruct v as [| b v]; [reflexivity |].
    destruct k; destruct b; discriminate.
  - destruct v as [| b v].
    + destruct l; destruct a; discriminate.
    + simpl in h. injection h as hab h.
      assert (a = b) by (destruct a, b; auto; discriminate).
      subst b. f_equal. exact (IH _ _ _ h).
Qed.

(** A machine computes at most one function (stated pointwise: Rocq has no
    function extensionality). *)
Theorem computes_unique : forall m f g p q, Computes m f p -> Computes m g q ->
  forall x, f x = g x.
Proof.
  intros m f g p q hf hg x.
  destruct (hf x) as [t1 [c [_ [hc [hcs [_ [k hck]]]]]]].
  destruct (hg x) as [t2 [d [_ [hd [hds [_ [l hdl]]]]]]].
  pose proof (reaches_exit_unique _ _ _ _ _ _ hc hd hcs hds). subst d.
  rewrite hck in hdl. exact (map_ofBool_blanks_injective _ _ _ _ hdl).
Qed.

Theorem similar_initial : forall y c off, state c = off -> tapeLeft c = [] ->
  forall k, tapeHead c :: tapeRight c = map ofBool y ++ blanks k ->
  Similar (shiftConfig off (initial y)) c.
Proof.
  intros y [cs cl ch cr] off hs hl k ht. simpl in hs, hl, ht. subst cs cl.
  unfold initial, initialSymbols.
  destruct (map ofBool y) as [| a rest].
  - destruct k as [| k]; [discriminate |]. simpl in ht. injection ht as h1 h2.
    subst ch cr. unfold Similar, shiftConfig. simpl.
    split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
    exists [], 0, k. split; reflexivity.
  - simpl in ht. injection ht as h1 h2. subst ch cr.
    unfold Similar, shiftConfig. simpl.
    split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
    exists rest, 0, k. simpl. rewrite app_nil_r. auto.
Qed.

Theorem polynomial_eval_mono : forall p n n', n <= n' -> evalPoly p n <= evalPoly p n'.
Proof.
  intros p n n' h. unfold evalPoly. apply Nat.mul_le_mono_l.
  apply Nat.pow_le_mono_l. lia.
Qed.

(** Composition.  Running a machine for [f] and then a machine [d] on its
    output is a run of the table [appendMachine m d] on the original input. *)
Theorem compose_run : forall m d f p, Computes m f p ->
  forall x t b, Run d (initial (f x)) t b ->
  exists t1, t1 <= evalPoly p (length x) /\
    Run (appendMachine m d) (initial x) (t1 + t) b.
Proof.
  intros m d f p hm x t b hr.
  destruct (hm x) as [t1 [c [ht1 [hreach [hstate [hleft [k htape]]]]]]].
  pose proof (similar_initial (f x) c (length (program m)) hstate hleft k htape) as hsim.
  exists t1. split; [exact ht1 |].
  apply reaches_run with c; [apply reaches_append; exact hreach |].
  apply run_of_similar with (shiftConfig (length (program m)) (initial (f x)));
    [apply run_append; exact hr | exact hsim].
Qed.

(** The time bound of a composition: [p(n) + p'(q(n))] is polynomially
    bounded. *)
Theorem compose_bound : forall p p' q : Polynomial,
  exists B : Polynomial, forall n,
    evalPoly p n + evalPoly p' (evalPoly q n) <= evalPoly B n.
Proof.
  intros p p' q. apply polynomiallyBounded_iff_polynomial.
  exact (polynomiallyBounded_add (evalPoly p) (fun n => evalPoly p' (evalPoly q n))
    (polynomiallyBounded_evalPoly p)
    (polynomiallyBounded_comp (evalPoly p') (evalPoly q)
      (polynomiallyBounded_evalPoly p') (polynomiallyBounded_evalPoly q))).
Qed.

(** A machine decides [L] within [p] on every word of the promise [Pr]. *)
Definition DecidesOn (m : Machine) (p : Polynomial) (Pr : Word -> Prop) (L : Language) : Prop :=
  forall x, Pr x -> exists t b, t <= evalPoly p (length x) /\ Run m (initial x) t b /\ b = L x.

(** Promise composition (machine construction).  A polynomial-time machine map
    [f] into the promise [Pr] that preserves the answer, followed by a
    polynomial-time machine that is correct only on [Pr], decides [L] in
    polynomial time. *)
Theorem inP_of_promise_reduction : forall (L M : Language) (Pr : Word -> Prop)
    (m d : Machine) (f : Word -> Word) (p p' : Polynomial),
  Computes m f p -> (forall x, Pr (f x)) -> (forall x, L x = M (f x)) ->
  DecidesOn d p' Pr M -> InP L.
Proof.
  intros L M Pr m d f p p' hm hinto hpres hd.
  destruct (computes_output_poly m f p hm) as [q hq].
  destruct (compose_bound p p' q) as [B hB].
  apply (inP_of_decidesWithin (appendMachine m d) B). intro x.
  destruct (hd (f x) (hinto x)) as [t2 [b [ht2 [hrun hb]]]].
  destruct (compose_run m d f p hm x t2 b hrun) as [t1 [ht1 hrun']].
  exists (t1 + t2), b. split; [| split; [exact hrun' | rewrite hb, hpres; reflexivity]].
  pose proof (polynomial_eval_mono p' _ _ (hq x)).
  pose proof (hB (length x)). lia.
Qed.

(** P is closed under polynomial-time reductions (machine construction). *)
Theorem inP_of_reduces : forall L L', PolyReduces L L' -> InP L' -> InP L.
Proof.
  intros L L' [m [f [p [hm hf]]]] hp.
  apply polyDec_iff_inP in hp. destruct hp as [d [p' hd]].
  apply (inP_of_promise_reduction L L' (fun _ => True) m d f p p' hm);
    [intro; exact I | exact hf |].
  intros y _. exact (hd y).
Qed.

(** ** P is closed under complement

    [flipMachine m] normalises every row of [m] to all four symbols, sends
    every out-of-table target to one extra state, and negates every halting
    answer, so a missing instruction (which rejects in [m]) accepts in
    [flipMachine m]. *)

Definition flipInstruction (n : nat) (i : Instruction) : Instruction :=
  match i with
  | halt b => halt (negb b)
  | move q w dir => move (Nat.min q n) w dir
  end.

Definition flipRow (n : nat) (row : list Instruction) : list Instruction :=
  map (fun i => flipInstruction n
         (match nth_error row i with Some ins => ins | None => halt false end))
    (seq 0 4).

Definition flipMachine (m : Machine) : Machine :=
  {| program := map (flipRow (length (program m))) (program m) ++
                  [repeat (halt true) 4] |}.

Theorem symbol_index_lt : forall a, symbolIndex a < 4.
Proof. intro a. destruct a; simpl; lia. Qed.

Theorem flip_instruction : forall m q a,
  instruction (flipMachine m) (Nat.min q (length (program m))) a =
    flipInstruction (length (program m)) (instruction m q a).
Proof.
  intros m q a. destruct (Nat.lt_ge_cases q (length (program m))) as [hq | hq].
  - rewrite Nat.min_l by lia. unfold instruction, flipMachine. simpl.
    rewrite nth_error_app1 by (rewrite length_map; exact hq).
    rewrite nth_error_map.
    destruct (nth_error (program m) q) as [row |] eqn:E.
    + simpl. unfold flipRow. destruct a; reflexivity.
    + apply nth_error_None in E. lia.
  - rewrite Nat.min_r by exact hq. rewrite (instruction_of_length_le m q a hq).
    unfold instruction, flipMachine. simpl.
    rewrite nth_error_app2 by (rewrite length_map; lia).
    rewrite length_map, Nat.sub_diag. destruct a; reflexivity.
Qed.

Definition normState (n : nat) (c : Config) : Config :=
  {| state := Nat.min (state c) n; tapeLeft := tapeLeft c; tapeHead := tapeHead c;
     tapeRight := tapeRight c |}.

Theorem moveHead_normState : forall n c q w dir,
  moveHead (normState n c) (Nat.min q n) w dir = normState n (moveHead c q w dir).
Proof.
  intros n [s l h r] q w dir. destruct dir, l, r; reflexivity.
Qed.

Theorem step_flip : forall m c,
  step (flipMachine m) (normState (length (program m)) c) =
    match step m c with
    | inl b => inl (negb b)
    | inr c' => inr (normState (length (program m)) c')
    end.
Proof.
  intros m c. unfold step.
  change (state (normState (length (program m)) c))
    with (Nat.min (state c) (length (program m))).
  change (tapeHead (normState (length (program m)) c)) with (tapeHead c).
  rewrite flip_instruction.
  destruct (instruction m (state c) (tapeHead c)) as [b | q w dir]; [reflexivity |].
  unfold flipInstruction. rewrite moveHead_normState. reflexivity.
Qed.

Theorem run_flip : forall m c t b, Run m c t b ->
  Run (flipMachine m) (normState (length (program m)) c) t (negb b).
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs _ IH].
  - apply run_halt. rewrite step_flip, hs. reflexivity.
  - apply run_next with (normState (length (program m)) c'); [| exact IH].
    rewrite step_flip, hs. reflexivity.
Qed.

Theorem normState_initial : forall n x, normState n (initial x) = initial x.
Proof.
  intros n x. unfold initial, initialSymbols, normState.
  destruct (map ofBool x); reflexivity.
Qed.

(** The complement of a language. *)
Definition complement (L : Language) : Language := fun x => negb (L x).

(** P is closed under complement (machine construction [flipMachine]). *)
Theorem inP_complement : forall L, InP L -> InP (complement L).
Proof.
  intros L h. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  apply (inP_of_decidesWithin (flipMachine m) p). intro x.
  destruct (hm x) as [t [b [ht [hr hb]]]].
  exists t, (negb b). split; [exact ht | split].
  - pose proof (run_flip _ _ _ _ hr) as H. rewrite normState_initial in H. exact H.
  - unfold complement. rewrite hb. reflexivity.
Qed.

(** Stated pointwise (no function extensionality). *)
Theorem complement_complement : forall L x, complement (complement L) x = L x.
Proof. intros L x. unfold complement. apply negb_involutive. Qed.

(** coNP in the shared model. *)
Definition InCoNP (L : Language) : Prop := InNP (complement L).

Definition NPEqualsCoNP : Prop := forall L, InNP L <-> InCoNP L.

(** P = NP implies NP = coNP (fully proved: [flipMachine] and [pToNP]). *)
Theorem npEqualsCoNP_of_pEqualsNP : PEqualsNP -> NPEqualsCoNP.
Proof.
  intros h L. split.
  - intro hL. apply pSubsetNP, inP_complement, h, hL.
  - intro hL. apply pSubsetNP.
    apply (inP_ext (complement (complement L))); [apply complement_complement |].
    apply inP_complement, h, hL.
Qed.

(** NP <> coNP implies P <> NP. *)
Theorem pNotEqualsNP_of_npNeCoNP : ~ NPEqualsCoNP -> PNotEqualsNP.
Proof. intros h hp. exact (h (npEqualsCoNP_of_pEqualsNP hp)). Qed.

(** ** NP-completeness *)

Definition NPHard (L : Language) : Prop := forall L', InNP L' -> PolyReduces L' L.

Definition NPComplete (L : Language) : Prop := InNP L /\ NPHard L.

(** An NP-complete language is in P if and only if P = NP. *)
Theorem npComplete_inP_iff : forall L, NPComplete L -> (InP L <-> PEqualsNP).
Proof.
  intros L h. split.
  - intros hL L' hL'. exact (inP_of_reduces L' L (proj2 h L' hL') hL).
  - intro hPNP. exact (hPNP L (proj1 h)).
Qed.

(** ** Non-vacuity: a language outside P

    Machines (and machine/polynomial pairs) are encoded injectively as words,
    with computable decoders.  The diagonal language rejects the code of every
    pair [(m, p)] such that [m] accepts that code within [p(|code|)] steps. *)

(** Prefix-free encodings: the code of [a] is not a proper prefix of another
    code. *)
Definition PrefixFree {A : Type} (e : A -> Word) : Prop :=
  forall a b r s, e a ++ r = e b ++ s -> a = b /\ r = s.

Fixpoint encNat (n : nat) : Word :=
  match n with
  | 0 => [false]
  | S n' => true :: encNat n'
  end.

Theorem encNat_prefixFree : PrefixFree encNat.
Proof.
  intro a. induction a as [| a IH]; intros b r s h; destruct b as [| b];
    simpl in h; try discriminate.
  - injection h as h. auto.
  - injection h as h. destruct (IH b r s h) as [-> ->]. auto.
Qed.

Definition directionIndex (d : Direction) : nat :=
  match d with left => 0 | right => 1 | stay => 2 end.

Definition encInstruction (i : Instruction) : Word :=
  match i with
  | halt b => [false; b]
  | move q w d => true :: (encNat q ++ encNat (symbolIndex w) ++ encNat (directionIndex d))
  end.

Theorem symbol_index_injective : forall a b, symbolIndex a = symbolIndex b -> a = b.
Proof. intros a b h. destruct a, b; simpl in h; auto; discriminate. Qed.

Theorem direction_index_injective : forall a b,
  directionIndex a = directionIndex b -> a = b.
Proof. intros a b h. destruct a, b; simpl in h; auto; discriminate. Qed.

Theorem encInstruction_prefixFree : PrefixFree encInstruction.
Proof.
  intros a b r s h. destruct a as [x | q w d], b as [y | q' w' d'];
    simpl in h; try discriminate.
  - injection h as -> h. auto.
  - injection h as h. rewrite <- !app_assoc in h.
    destruct (encNat_prefixFree _ _ _ _ h) as [hq h1].
    destruct (encNat_prefixFree _ _ _ _ h1) as [hw h2].
    destruct (encNat_prefixFree _ _ _ _ h2) as [hd h3].
    subst q'. apply symbol_index_injective in hw. apply direction_index_injective in hd.
    subst. auto.
Qed.

Fixpoint encList {A : Type} (e : A -> Word) (l : list A) : Word :=
  match l with
  | [] => [false]
  | a :: l' => true :: (e a ++ encList e l')
  end.

Theorem encList_prefixFree : forall {A : Type} (e : A -> Word),
  PrefixFree e -> PrefixFree (encList e).
Proof.
  intros A e he a. induction a as [| x l IH]; intros b r s h;
    destruct b as [| y l']; simpl in h; try discriminate.
  - injection h as h. auto.
  - injection h as h. rewrite <- !app_assoc in h.
    destruct (he _ _ _ _ h) as [hxy h'].
    destruct (IH _ _ _ h') as [hl h''].
    subst. auto.
Qed.

(** The code of a machine: its instruction table, row by row. *)
Definition encMachine (m : Machine) : Word := encList (encList encInstruction) (program m).

Theorem encMachine_injective : forall m m', encMachine m = encMachine m' -> m = m'.
Proof.
  intros [p] [p'] h. unfold encMachine in h. simpl in h.
  assert (h' : encList (encList encInstruction) p ++ [] =
               encList (encList encInstruction) p' ++ []) by (rewrite h; reflexivity).
  destruct (encList_prefixFree _ (encList_prefixFree _ encInstruction_prefixFree)
              _ _ _ _ h') as [-> _].
  reflexivity.
Qed.

(** Machines paired with explicit polynomials also have an injective
    encoding. *)
Definition encMachinePoly (x : Machine * Polynomial) : Word :=
  encMachine (fst x) ++ encNat (coefficient (snd x)) ++ encNat (degree (snd x)).

Theorem encMachinePoly_injective : forall x y,
  encMachinePoly x = encMachinePoly y -> x = y.
Proof.
  intros [[p] [c d]] [[p'] [c' d']] h.
  unfold encMachinePoly, encMachine in h. simpl in h.
  destruct (encList_prefixFree _ (encList_prefixFree _ encInstruction_prefixFree)
              _ _ _ _ h) as [hm h1].
  destruct (encNat_prefixFree _ _ _ _ h1) as [hc h2].
  assert (h3 : encNat d ++ [] = encNat d' ++ []) by (rewrite !app_nil_r; exact h2).
  destruct (encNat_prefixFree _ _ _ _ h3) as [hd _].
  subst. reflexivity.
Qed.

(** *** Computable decoders (left inverses of the encodings) *)

Definition obind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with Some a => f a | None => None end.

Fixpoint decNat (w : Word) : option (nat * Word) :=
  match w with
  | [] => None
  | false :: r => Some (0, r)
  | true :: r => obind (decNat r) (fun '(n, r') => Some (S n, r'))
  end.

Theorem decNat_encNat : forall n r, decNat (encNat n ++ r) = Some (n, r).
Proof.
  induction n as [| n IH]; intro r; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Definition symbolOfIndex (i : nat) : option Symbol :=
  match i with
  | 0 => Some blank | 1 => Some zero | 2 => Some one | 3 => Some separator
  | _ => None
  end.

Definition directionOfIndex (i : nat) : option Direction :=
  match i with 0 => Some left | 1 => Some right | 2 => Some stay | _ => None end.

Definition decInstruction (w : Word) : option (Instruction * Word) :=
  match w with
  | false :: b :: r => Some (halt b, r)
  | true :: r =>
      obind (decNat r) (fun '(q, r1) =>
      obind (decNat r1) (fun '(i, r2) =>
      obind (symbolOfIndex i) (fun a =>
      obind (decNat r2) (fun '(j, r3) =>
      obind (directionOfIndex j) (fun d => Some (move q a d, r3))))))
  | _ => None
  end.

Theorem decInstruction_encInstruction : forall i r,
  decInstruction (encInstruction i ++ r) = Some (i, r).
Proof.
  intros [b | q w d] r; simpl; [reflexivity |].
  rewrite <- !app_assoc, decNat_encNat. simpl.
  rewrite decNat_encNat. simpl.
  destruct w; simpl; rewrite decNat_encNat; destruct d; reflexivity.
Qed.

(** Every list element costs at least one marker bit, so [length w] is enough
    fuel. *)
Fixpoint decListFuel {A : Type} (d : Word -> option (A * Word)) (fuel : nat) (w : Word)
    : option (list A * Word) :=
  match fuel with
  | 0 => None
  | S f =>
      match w with
      | false :: r => Some ([], r)
      | true :: r =>
          obind (d r) (fun '(a, r1) =>
          obind (decListFuel d f r1) (fun '(l, r2) => Some (a :: l, r2)))
      | [] => None
      end
  end.

Definition decList {A : Type} (d : Word -> option (A * Word)) (w : Word)
    : option (list A * Word) :=
  decListFuel d (length w) w.

Lemma length_encList : forall {A : Type} (e : A -> Word) l,
  length l < length (encList e l).
Proof.
  intros A e l. induction l as [| a l IH]; simpl; [lia |].
  rewrite length_app. lia.
Qed.

Theorem decListFuel_encList : forall {A : Type} (e : A -> Word) (d : Word -> option (A * Word)),
  (forall a r, d (e a ++ r) = Some (a, r)) ->
  forall l r fuel, length l < fuel -> decListFuel d fuel (encList e l ++ r) = Some (l, r).
Proof.
  intros A e d hd l. induction l as [| a l IH]; intros r fuel hf;
    (destruct fuel as [| fuel]; [lia |]); simpl; [reflexivity |].
  rewrite <- app_assoc, hd. simpl. rewrite IH by (simpl in hf; lia). reflexivity.
Qed.

Theorem decList_encList : forall {A : Type} (e : A -> Word) (d : Word -> option (A * Word)),
  (forall a r, d (e a ++ r) = Some (a, r)) ->
  forall l r, decList d (encList e l ++ r) = Some (l, r).
Proof.
  intros A e d hd l r. unfold decList. apply (decListFuel_encList e d hd).
  pose proof (length_encList e l). rewrite length_app. lia.
Qed.

(** Parse a machine code from the front of a word. *)
Definition decMachineFront (w : Word) : option (Machine * Word) :=
  obind (decList (decList decInstruction) w) (fun '(p, r) => Some ({| program := p |}, r)).

Theorem decMachineFront_encMachine : forall m r,
  decMachineFront (encMachine m ++ r) = Some (m, r).
Proof.
  intros [p] r. unfold decMachineFront, encMachine. simpl.
  rewrite (decList_encList (encList encInstruction) (decList decInstruction)).
  - reflexivity.
  - apply decList_encList. apply decInstruction_encInstruction.
Qed.

(** A total decoder for machines (trailing bits are ignored). *)
Definition decMachine (w : Word) : option Machine :=
  obind (decMachineFront w) (fun '(m, _) => Some m).

Theorem decMachine_encMachine : forall m, decMachine (encMachine m) = Some m.
Proof.
  intro m. unfold decMachine. rewrite <- (app_nil_r (encMachine m)).
  rewrite decMachineFront_encMachine. reflexivity.
Qed.

(** A total decoder for machine/polynomial pairs (trailing bits are
    ignored). *)
Definition decMachinePoly (w : Word) : option (Machine * Polynomial) :=
  obind (decMachineFront w) (fun '(m, r1) =>
  obind (decNat r1) (fun '(c, r2) =>
  obind (decNat r2) (fun '(k, _) =>
  Some (m, {| coefficient := c; degree := k |})))).

Theorem decMachinePoly_encMachinePoly : forall x,
  decMachinePoly (encMachinePoly x) = Some x.
Proof.
  intros [m [c k]]. unfold decMachinePoly, encMachinePoly. simpl.
  rewrite decMachineFront_encMachine. simpl.
  rewrite decNat_encNat. simpl.
  rewrite <- (app_nil_r (encNat k)), decNat_encNat. reflexivity.
Qed.

(** *** A step-bounded interpreter *)

(** Run [m] from [c] for at most [fuel] steps. *)
Fixpoint runFor (m : Machine) (c : Config) (fuel : nat) : option bool :=
  match fuel with
  | 0 => None
  | S f => match step m c with
           | inl b => Some b
           | inr c' => runFor m c' f
           end
  end.

Theorem runFor_of_run : forall m c t b, Run m c t b ->
  forall fuel, t <= fuel -> runFor m c fuel = Some b.
Proof.
  intros m c t b h. induction h as [c b hs | c c' t b hs _ IH]; intros fuel hf;
    (destruct fuel as [| fuel]; [lia |]); simpl; rewrite hs; [reflexivity |].
  apply IH. lia.
Qed.

Theorem run_of_runFor : forall m fuel c b, runFor m c fuel = Some b ->
  exists t, t <= fuel /\ Run m c t b.
Proof.
  intros m fuel. induction fuel as [| fuel IH]; intros c b h; simpl in h;
    [discriminate |].
  destruct (step m c) as [b' | c'] eqn:hs.
  - injection h as <-. exists 1. split; [lia | apply run_halt; exact hs].
  - destruct (IH _ _ h) as [t [ht hr]]. exists (S t).
    split; [lia | apply run_next with c'; assumption].
Qed.

(** *** The diagonal language *)

(** The language of the pair [(m, p)] as seen by the diagonal: accept iff [m]
    accepts within [p(|w|)] steps. *)
Definition clockedLanguage (x : Machine * Polynomial) : Language := fun w =>
  match runFor (fst x) (initial w) (evalPoly (snd x) (length w)) with
  | Some true => true
  | _ => false
  end.

(** The diagonal language: [w] is in it unless [w] is the code of a pair
    [(m, p)] such that [m] accepts [w] within [p(|w|)] steps.  Unlike the
    Lean [Diag] (noncomputable, unbounded runs), this one is computable. *)
Definition Diag : Language := fun w =>
  match decMachinePoly w with
  | Some x => negb (clockedLanguage x w)
  | None => true
  end.

(** Diagonalisation.  No polynomial-time machine decides [Diag]. *)
Theorem diag_not_inP : ~ InP Diag.
Proof.
  intros [P hP].
  set (w := encMachinePoly (p_machine P, p_bound P)).
  destruct (p_terminates P w) as [t [b [ht hr]]].
  pose proof (p_correct P w t b hr) as hc. rewrite hP in hc.
  assert (hD : Diag w = negb b).
  { unfold Diag, w. rewrite decMachinePoly_encMachinePoly.
    unfold clockedLanguage. simpl fst. simpl snd. fold w.
    rewrite (runFor_of_run _ _ _ _ hr _ ht). destruct b; reflexivity. }
  rewrite hD in hc. destruct b; simpl in hc; destruct hc as [h1 h2].
  - discriminate (h2 eq_refl).
  - discriminate (h1 eq_refl).
Qed.

(** Statements [InP L] (equivalently [PolyDec L]) are not provable for every
    language: the machine-level obligations are not vacuous. *)
Theorem exists_not_inP : exists L : Language, ~ InP L.
Proof. exists Diag. exact diag_not_inP. Qed.

Theorem not_forall_polyDec : ~ (forall L : Language, PolyDec L).
Proof. intro h. apply diag_not_inP. apply polyDec_iff_inP. apply h. Qed.

(** Cantor's argument over words.  A family of languages indexed by a type
    whose encoding into words has a computable left inverse misses some
    language.  (Lean assumes only injectivity and uses classical logic; the
    left inverse [d] implies injectivity, see
    [injective_of_left_inverse].) *)
Theorem exists_language_not_in_family : forall {T : Type} (e : T -> Word)
    (d : Word -> option T), (forall a, d (e a) = Some a) ->
  forall F : T -> Language, exists L : Language, forall a, F a <> L.
Proof.
  intros T e d hd F.
  exists (fun w => match d w with Some a => negb (F a w) | None => true end).
  intros a hFa.
  pose proof (f_equal (fun G : Language => G (e a)) hFa) as hw. simpl in hw.
  rewrite hd in hw. destruct (F a (e a)); discriminate.
Qed.

Theorem injective_of_left_inverse : forall {T : Type} (e : T -> Word)
    (d : Word -> option T), (forall a, d (e a) = Some a) ->
  forall a b, e a = e b -> a = b.
Proof.
  intros T e d hd a b h. pose proof (hd a) as ha. rewrite h, hd in ha.
  injection ha as ->. reflexivity.
Qed.

(** Instances: families indexed by machines, and by machine/polynomial
    pairs. *)
Theorem exists_language_not_in_machine_family : forall F : Machine -> Language,
  exists L : Language, forall m, F m <> L.
Proof.
  intro F. exact (exists_language_not_in_family encMachine decMachine
    decMachine_encMachine F).
Qed.

Theorem exists_language_not_in_machinePoly_family :
  forall F : Machine * Polynomial -> Language,
  exists L : Language, forall x, F x <> L.
Proof.
  intro F. exact (exists_language_not_in_family encMachinePoly decMachinePoly
    decMachinePoly_encMachinePoly F).
Qed.

(** ** CNF formulas and SAT as a language

    Tokens are bit pairs: [11] is a unary tick of the variable index, [0p]
    ends a literal with polarity [p], [10] ends a clause.  The literal
    [(v, p)] is [11^v 0p]; a clause is its literals followed by [10]. *)

(** A literal: variable index and polarity ([pos = true] means [x_var]). *)
Record Lit := mkLit { var : nat; pos : bool }.
Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition evalLit (a : Assignment) (l : Lit) : bool := Bool.eqb (a (var l)) (pos l).

Fixpoint evalClause (a : Assignment) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' => evalLit a l || evalClause a c'
  end.

Fixpoint evalCNF (a : Assignment) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | c :: phi' => evalClause a c && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a : Assignment, evalCNF a phi = true.

(** *** Brute force over the variables that occur (moved from Idea 01) *)

(** All variables of [phi] are [< n]. *)
Definition VarsBelow (n : nat) (phi : CNF) : Prop :=
  forall c, In c phi -> forall l, In l c -> var l < n.

Theorem evalClause_congr : forall (a b : Assignment) (n : nat) (c : Clause),
  (forall i, i < n -> a i = b i) -> (forall l, In l c -> var l < n) ->
  evalClause a c = evalClause b c.
Proof.
  intros a b n c hab; induction c as [| l c IH]; intros hc; simpl; auto.
  unfold evalLit. rewrite (hab (var l) (hc l (or_introl eq_refl))).
  rewrite IH; auto. intros l' hl'; apply hc; simpl; auto.
Qed.

(** Formulas with variables [< n] only look at the first [n] values. *)
Theorem evalCNF_congr : forall (a b : Assignment) (n : nat) (phi : CNF),
  (forall i, i < n -> a i = b i) -> VarsBelow n phi -> evalCNF a phi = evalCNF b phi.
Proof.
  intros a b n phi hab; induction phi as [| c phi IH]; intros hphi; simpl; auto.
  rewrite (evalClause_congr a b n c hab (hphi c (or_introl eq_refl))).
  rewrite IH; auto. intros c' hc'; apply hphi; simpl; auto.
Qed.

(** *** Enumerating all assignments *)

(** All [2^n] bit vectors of length [n] (bit [0] is the head). *)
Fixpoint allAssignments (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allAssignments n') ++ map (cons true) (allAssignments n')
  end.

(** Bit vector to assignment: index [i] maps to bit [i], [false] beyond the
    end. *)
Fixpoint toAssign (v : list bool) (i : nat) : bool :=
  match v, i with
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v', S i' => toAssign v' i'
  end.

(** The first [n] values of an assignment, as a bit vector. *)
Fixpoint prefixOf (a : Assignment) (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => a 0 :: prefixOf (fun i => a (S i)) n'
  end.

(** The enumeration contains exactly the vectors of length [n]. *)
Theorem mem_allAssignments_iff : forall (n : nat) (v : list bool),
  In v (allAssignments n) <-> length v = n.
Proof.
  intro n. induction n as [| n IH]; intros v.
  - destruct v as [| b v]; simpl; split; intros H; auto; try discriminate.
    destruct H as [H | H]; [discriminate | contradiction].
  - destruct v as [| b v]; simpl; rewrite in_app_iff, !in_map_iff; split.
    + intros [[w [Hw _]] | [w [Hw _]]]; discriminate.
    + intros H; discriminate.
    + intros [[w [Hw Hin]] | [w [Hw Hin]]]; injection Hw; intros; subst;
        f_equal; apply IH; auto.
    + intros H; injection H; intros H'; destruct b.
      * right; exists v; split; auto; apply IH; auto.
      * left; exists v; split; auto; apply IH; auto.
Qed.

Theorem length_prefixOf : forall (a : Assignment) (n : nat), length (prefixOf a n) = n.
Proof. intros a n; revert a; induction n; intros a; simpl; auto. Qed.

Theorem toAssign_prefixOf : forall (a : Assignment) (n i : nat),
  i < n -> toAssign (prefixOf a n) i = a i.
Proof.
  intros a n; revert a; induction n as [| n IH]; intros a i H; [lia |].
  destruct i as [| i]; simpl; auto.
  apply (IH (fun j => a (S j))); lia.
Qed.

(** *** The brute-force decider *)

(** Try every vector of length [n]. *)
Definition bruteForce (n : nat) (phi : CNF) : bool :=
  existsb (fun v => evalCNF (toAssign v) phi) (allAssignments n).

(** Soundness: acceptance yields a satisfying assignment. *)
Theorem brute_force_sound : forall (n : nat) (phi : CNF),
  bruteForce n phi = true -> Satisfiable phi.
Proof.
  intros n phi; unfold bruteForce; intros H; apply existsb_exists in H.
  destruct H as [v [_ Hv]]; exists (toAssign v); auto.
Qed.

(** Completeness: if all variables are [< n], every satisfiable formula is
    accepted, because every assignment agrees on [0, ..., n-1] with a listed
    vector. *)
Theorem brute_force_complete : forall (n : nat) (phi : CNF),
  VarsBelow n phi -> Satisfiable phi -> bruteForce n phi = true.
Proof.
  intros n phi Hphi [a Ha]; unfold bruteForce; apply existsb_exists.
  exists (prefixOf a n); split.
  - apply mem_allAssignments_iff, length_prefixOf.
  - rewrite (evalCNF_congr (toAssign (prefixOf a n)) a n phi); auto.
    intros i Hi; apply toAssign_prefixOf; auto.
Qed.

(** *** Number of variables *)

Fixpoint clauseBound (c : Clause) : nat :=
  match c with
  | [] => 0
  | l :: c' => Nat.max (S (var l)) (clauseBound c')
  end.

(** One more than the largest variable index (0 for variable-free formulas). *)
Fixpoint numVars (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => Nat.max (clauseBound c) (numVars phi')
  end.

Theorem lt_clauseBound : forall (c : Clause) l, In l c -> var l < clauseBound c.
Proof.
  intro c; induction c as [| l c IH]; intros l' Hl'; [contradiction |].
  change (clauseBound (l :: c)) with (Nat.max (S (var l)) (clauseBound c)).
  destruct Hl' as [H | H]; [subst; lia |]. specialize (IH l' H); lia.
Qed.

Theorem varsBelow_numVars : forall phi : CNF, VarsBelow (numVars phi) phi.
Proof.
  intro phi; induction phi as [| c phi IH]; intros c' Hc' l Hl; [contradiction |].
  change (numVars (c :: phi)) with (Nat.max (clauseBound c) (numVars phi)).
  destruct Hc' as [H | H].
  - subst; pose proof (lt_clauseBound c' l Hl); lia.
  - pose proof (IH c' H l Hl); lia.
Qed.

(** The uniform decider: brute force over the variables that occur. *)
Theorem bruteForce_correct : forall phi : CNF,
  bruteForce (numVars phi) phi = true <-> Satisfiable phi.
Proof.
  intro phi.
  split; [apply brute_force_sound | apply brute_force_complete, varsBelow_numVars].
Qed.

(** *** The word encoding *)

Fixpoint ticks (k : nat) : list bool :=
  match k with
  | 0 => []
  | S k' => true :: true :: ticks k'
  end.

Definition encodeLit (l : Lit) : list bool := ticks (var l) ++ [false; pos l].

Fixpoint encodeClause (c : Clause) : list bool :=
  match c with
  | [] => [true; false]
  | l :: c' => encodeLit l ++ encodeClause c'
  end.

Fixpoint encodeCNF (phi : CNF) : list bool :=
  match phi with
  | [] => []
  | c :: phi' => encodeClause c ++ encodeCNF phi'
  end.

Fixpoint decodeAux (w : list bool) (k : nat) (cur : Clause) : CNF :=
  match w with
  | true :: true :: rest => decodeAux rest (S k) cur
  | false :: p :: rest => decodeAux rest 0 (cur ++ [mkLit k p])
  | true :: false :: rest => cur :: decodeAux rest 0 []
  | _ => []
  end.

Definition decode (w : list bool) : CNF := decodeAux w 0 [].

Theorem decodeAux_ticks : forall (v : nat) (r : list bool) (k : nat) (cur : Clause),
  decodeAux (ticks v ++ r) k cur = decodeAux r (k + v) cur.
Proof.
  intros v r; induction v as [| v IH]; intros k cur; simpl.
  - rewrite Nat.add_0_r; auto.
  - rewrite IH; f_equal; lia.
Qed.

Theorem decodeAux_clause : forall (c : Clause) (r : list bool) (cur : Clause),
  decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 [].
Proof.
  intros c r; induction c as [| [v p] c IH]; intros cur; simpl.
  - rewrite app_nil_r; auto.
  - unfold encodeLit; simpl. rewrite <- !app_assoc, decodeAux_ticks. simpl.
    rewrite IH, <- app_assoc; auto.
Qed.

Theorem decode_encode : forall phi : CNF, decode (encodeCNF phi) = phi.
Proof.
  intro phi; unfold decode; induction phi as [| c phi IH]; simpl; auto.
  rewrite decodeAux_clause, IH; auto.
Qed.

(** Distinct formulas have distinct encodings. *)
Theorem encode_injective : forall phi psi : CNF, encodeCNF phi = encodeCNF psi -> phi = psi.
Proof.
  intros phi psi H; rewrite <- (decode_encode phi), H; apply decode_encode.
Qed.

(** SAT as a language of the shared model.  Every word denotes a formula
    through the total parser [decode] (malformed tails are dropped), so a
    machine for SAT never needs a separate well-formedness check; on
    encodings, [decode] inverts [encodeCNF] ([decode_encode]).  The definition
    is the exponential brute-force search, which is computable and correct
    ([sat_iff]). *)
Definition SAT : Language := fun w => bruteForce (numVars (decode w)) (decode w).

Theorem sat_iff : forall w : Word, SAT w = true <-> Satisfiable (decode w).
Proof. intro w. exact (bruteForce_correct (decode w)). Qed.

Theorem sat_encode : forall phi : CNF, SAT (encodeCNF phi) = true <-> Satisfiable phi.
Proof. intro phi. rewrite sat_iff, decode_encode. reflexivity. Qed.

(** ** The Cook-Levin theorem, stated in this model

    [CookLevin] is a precise proposition about [Machine], [Run] and the class
    NP of [ClassNP].  It is a known theorem (Cook 1971, Levin 1973; mechanised
    for a different machine model by Gaeher and Kunze, ITP 2021).  The
    membership half [SATInNP] is proved in [SATVerifier.v] ([satInNP], a
    45-state verifier that halts within [5 (n + 1)^2] steps), which imports
    this file.  The hardness half [SATHard] needs the tableau reduction and is
    NOT proved here.  Idea files that use it take [SATHard] or [CookLevin] as
    a named explicit hypothesis (a premise of a theorem, never an [Axiom]). *)

(** SAT is in NP: a polynomial-time machine verifier for SAT. *)
Definition SATInNP : Prop := InNP SAT.

(** SAT is NP-hard: every NP language reduces to SAT by a polynomial-time
    machine. *)
Definition SATHard : Prop := NPHard SAT.

Definition CookLevin : Prop := NPComplete SAT.

Theorem cookLevin_iff : CookLevin <-> SATInNP /\ SATHard.
Proof. reflexivity. Qed.

(** A polynomial-time machine decider for SAT gives P = NP; needs only the
    hardness half of Cook-Levin. *)
Theorem pEqualsNP_of_inP_sat : SATHard -> InP SAT -> PEqualsNP.
Proof. intros hard h L hL. exact (inP_of_reduces L SAT (hard L hL) h). Qed.

(** P = NP gives a polynomial-time machine decider for SAT; needs only the
    membership half of Cook-Levin. *)
Theorem inP_sat_of_pEqualsNP : SATInNP -> PEqualsNP -> InP SAT.
Proof. intros mem h. exact (h SAT mem). Qed.

(** Given Cook-Levin, deciding SAT in polynomial time on the shared machine
    model is equivalent to P = NP. *)
Theorem inP_sat_iff : CookLevin -> (InP SAT <-> PEqualsNP).
Proof. intro hCL. exact (npComplete_inP_iff SAT hCL). Qed.

(** A decider for [SAT] decides satisfiability on encodings of formulas. *)
Theorem inP_sat_on_encodings : InP SAT ->
  exists (m : Machine) (p : Polynomial), forall phi : CNF, exists t b,
    t <= evalPoly p (length (encodeCNF phi)) /\ Run m (initial (encodeCNF phi)) t b /\
    (b = true <-> Satisfiable phi).
Proof.
  intro h. apply polyDec_iff_inP in h. destruct h as [m [p hm]].
  exists m, p. intro phi.
  destruct (hm (encodeCNF phi)) as [t [b [ht [hr hb]]]].
  exists t, b. split; [exact ht | split; [exact hr |]].
  rewrite hb. apply sat_encode.
Qed.
