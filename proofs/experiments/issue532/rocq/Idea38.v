(* Issue #532, Idea 38: relativization audit (oracle query lower bound).

   Rocq counterpart of ../lean/Idea38.lean; theorem names are aligned.
   Deterministic oracle computations are adaptive decision trees over an oracle
   O : nat -> bool. A tree of depth < N cannot distinguish the all-false oracle
   from some oracle that is true at exactly one position j < N, so it cannot
   decide "exists j < N, O j = true" (the combinatorial core of Baker-Gill-Solovay).
   The bound is exact (orTree), a guessed position is verified with one query,
   and polynomial-depth families fail on 2^n positions (bgs_core).
   Abstractly, a relativizing proof method settles no statement that holds for
   one oracle and fails for another; NonrelativizingIngredientFor is the
   generic schema over a free proof method.

   Machine part, on the oracle machines of Idea 16 (OMachine extends Machine by
   a query instruction): the explicit one-query oracle machine testVerifier
   shows testLangO A in NP^A for every oracle A (testLangO_inNPO);
   BGSTestSeparation (the BGS stage construction, a known theorem stated as a
   named premise) gives Idea 16's BGSSeparation; and under the BGS premises a
   relativizing method proves neither P^A = NP^A nor its negation for all
   oracles (machineRelativizing_cannot_settle).  The BGS oracle constructions
   themselves are not formalized.

   Differences from Lean:
   - nonrelativizing_iff takes the explicit premise ExcludedMiddle for its
     backward direction (Lean uses Classical.byContradiction); no classical
     library is imported.
   - testLangO is the computable bounded search over wordsUpTo (from Idea 16)
     instead of a classical decide; testLangO_iff gives the Lean meaning.
   - Constructors of oracle instructions are obase/oquery (Idea 16). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue532.rocq Require Import Idea16.

Theorem tested : exists property : bool -> Prop, property false /\ ~ property true.
Proof. exists (fun oracle => oracle = false). split; [reflexivity | discriminate]. Qed.

(* Decision trees with oracle queries. *)

Inductive Tree : Type :=
| leaf (b : bool)
| query (i : nat) (t0 t1 : Tree).

Fixpoint eval (O : nat -> bool) (T : Tree) : bool :=
  match T with
  | leaf b => b
  | query i t0 t1 => if O i then eval O t1 else eval O t0
  end.

Fixpoint depth (T : Tree) : nat :=
  match T with
  | leaf _ => 0
  | query _ t0 t1 => S (Nat.max (depth t0) (depth t1))
  end.

Fixpoint falsePath (T : Tree) : list nat :=
  match T with
  | leaf _ => []
  | query i t0 _ => i :: falsePath t0
  end.

Definition allFalse : nat -> bool := fun _ => false.

Definition single (j : nat) : nat -> bool := fun i => Nat.eqb i j.

Theorem falsePath_length : forall T, length (falsePath T) <= depth T.
Proof.
  induction T as [b | i t0 IH0 t1 IH1]; simpl; [lia|].
  pose proof (Nat.le_max_l (depth t0) (depth t1)). lia.
Qed.

Theorem eval_single_of_not_mem : forall T j,
  ~ In j (falsePath T) -> eval (single j) T = eval allFalse T.
Proof.
  induction T as [b | i t0 IH0 t1 IH1]; intros j Hj; simpl; [reflexivity|].
  simpl in Hj.
  assert (Hij : Nat.eqb i j = false).
  { apply Nat.eqb_neq. intro E. apply Hj. left. exact E. }
  unfold single at 1. rewrite Hij. unfold allFalse at 1.
  apply IH0. intro H. apply Hj. right. exact H.
Qed.

Theorem exists_not_mem : forall N (L : list nat),
  length L < N -> exists j, j < N /\ ~ In j L.
Proof.
  induction N as [|N IH]; intros L HL; [lia|].
  destruct (In_dec Nat.eq_dec N L) as [HN | HN].
  - pose proof (remove_length_lt Nat.eq_dec L N HN) as Hlen.
    destruct (IH (remove Nat.eq_dec N L) ltac:(lia)) as [j [Hj HjL]].
    exists j. split; [lia|].
    intro Hin. apply HjL. apply in_in_remove; [lia | exact Hin].
  - exists N. split; [lia | exact HN].
Qed.

(* Shallow trees miss a position. *)
Theorem shallow_tree_misses : forall T N,
  depth T < N -> exists j, j < N /\ eval allFalse T = eval (single j) T.
Proof.
  intros T N H.
  pose proof (falsePath_length T).
  destruct (exists_not_mem N (falsePath T) ltac:(lia)) as [j [Hj HjL]].
  exists j. split; [exact Hj|].
  symmetry. apply eval_single_of_not_mem. exact HjL.
Qed.

(* Query lower bound (BGS core). *)
Theorem no_shallow_tree_decides_or : forall T N,
  depth T < N ->
  ~ (forall O : nat -> bool, eval O T = true <-> exists j, j < N /\ O j = true).
Proof.
  intros T N H Hdec.
  destruct (shallow_tree_misses T N H) as [j [Hj Heq]].
  assert (H1 : eval (single j) T = true).
  { apply Hdec. exists j. split; [exact Hj|]. unfold single. apply Nat.eqb_refl. }
  assert (H0 : eval allFalse T <> true).
  { intro Ht. apply Hdec in Ht. destruct Ht as [k [_ Hk]]. discriminate Hk. }
  apply H0. rewrite Heq. exact H1.
Qed.

(* The bound is exact, and one nondeterministic query suffices. *)

Fixpoint orTree (N : nat) : Tree :=
  match N with
  | 0 => leaf false
  | S N' => query N' (orTree N') (leaf true)
  end.

Theorem orTree_depth : forall N, depth (orTree N) = N.
Proof.
  induction N as [|N IH]; simpl; [reflexivity|].
  rewrite IH. f_equal. apply Nat.max_l. lia.
Qed.

Theorem orTree_correct : forall (O : nat -> bool) N,
  eval O (orTree N) = true <-> exists j, j < N /\ O j = true.
Proof.
  intros O N. induction N as [|N IH]; simpl.
  - split; [discriminate | intros [j [Hj _]]; lia].
  - destruct (O N) eqn:HN.
    + split; [intros _; exists N; split; [lia | exact HN] | reflexivity].
    + rewrite IH. split.
      * intros [j [Hj HOj]]. exists j. split; [lia | exact HOj].
      * intros [j [Hj HOj]]. destruct (Nat.eq_dec j N) as [E | E].
        -- subst j. rewrite HN in HOj. discriminate.
        -- exists j. split; [lia | exact HOj].
Qed.

Theorem verifier_one_query : forall (O : nat -> bool) N,
  (exists j, j < N /\ O j = true) <->
  exists j, j < N /\ eval O (query j (leaf false) (leaf true)) = true.
Proof.
  intros O N. split.
  - intros [j [Hj HOj]]. exists j. split; [exact Hj|]. simpl. rewrite HOj. reflexivity.
  - intros [j [Hj Hev]]. exists j. split; [exact Hj|]. simpl in Hev.
    destruct (O j); [reflexivity | discriminate].
Qed.

(* Polynomial depth against 2^n positions. *)

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

(* BGS core, polynomial form. *)
Theorem bgs_core : forall (trees : nat -> Tree) c k,
  (forall n, depth (trees n) <= c * (n + 1) ^ k) ->
  exists n, ~ (forall O : nat -> bool,
    eval O (trees n) = true <-> exists j, j < 2 ^ n /\ O j = true).
Proof.
  intros trees c k Hdepth.
  exists (2 ^ (2 * (c + k) + 1)).
  apply no_shallow_tree_decides_or.
  eapply Nat.le_lt_trans; [apply Hdepth|].
  apply exp_beats_poly. lia.
Qed.

(* Relativizing proof methods. *)

Definition Relativizing (Proves : ((nat -> bool) -> Prop) -> Prop) : Prop :=
  forall S, Proves S -> forall O, S O.

Theorem relativizing_cannot_prove : forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  Relativizing Proves -> forall (S : (nat -> bool) -> Prop) O, ~ S O -> ~ Proves S.
Proof. intros Proves Hrel S O HO HS. apply HO. apply (Hrel S HS O). Qed.

(* BGS meta-theorem (abstract). *)
Theorem relativizing_cannot_decide : forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  Relativizing Proves -> forall (S : (nat -> bool) -> Prop) (A B : nat -> bool),
  S A -> ~ S B -> ~ Proves S /\ ~ Proves (fun O => ~ S O).
Proof.
  intros Proves Hrel S A B HA HB. split.
  - apply (relativizing_cannot_prove Proves Hrel S B HB).
  - apply (relativizing_cannot_prove Proves Hrel (fun O => ~ S O) A).
    intro H. apply H. exact HA.
Qed.

(** Generic schema over a free proof method [Proves] (not a machine-level
    statement): the method proves some statement that fails relative to some
    oracle.  The machine-level barrier is machineRelativizing_cannot_settle. *)
Definition NonrelativizingIngredientFor (Proves : ((nat -> bool) -> Prop) -> Prop) : Prop :=
  exists S O, Proves S /\ ~ S O.

Theorem nonrelativizing_needed : forall (Proves : ((nat -> bool) -> Prop) -> Prop)
  (S : (nat -> bool) -> Prop) (A B : nat -> bool),
  S A -> ~ S B -> (Proves S \/ Proves (fun O => ~ S O)) ->
  NonrelativizingIngredientFor Proves.
Proof.
  intros Proves S A B HA HB [H | H].
  - exists S, B. split; assumption.
  - exists (fun O => ~ S O), A. split; [exact H|]. intro H'. apply H'. exact HA.
Qed.

(** Excluded middle, as an explicit premise (the Lean proof uses
    Classical.byContradiction; no classical library is imported here). *)
Definition ExcludedMiddle : Prop := forall P : Prop, P \/ ~ P.

(* NonrelativizingIngredientFor is exactly the failure of Relativizing. The
   backward direction needs excluded middle, taken as the premise
   ExcludedMiddle; every other theorem in this file is constructive. *)
Theorem nonrelativizing_iff : ExcludedMiddle ->
  forall (Proves : ((nat -> bool) -> Prop) -> Prop),
  NonrelativizingIngredientFor Proves <-> ~ Relativizing Proves.
Proof.
  intros em Proves. split.
  - intros [S [O [HS HO]]] Hrel. apply HO. apply (Hrel S HS O).
  - intros Hnot. destruct (em (NonrelativizingIngredientFor Proves)) as [H | Hno];
      [exact H |].
    exfalso. apply Hnot. intros S HS O.
    destruct (em (S O)) as [HO | HO]; [exact HO |].
    exfalso. apply Hno. exists S, O. split; assumption.
Qed.

Example orTree_check : eval (single 1) (orTree 2) = true.
Proof. reflexivity. Qed.


(* ======================================================================= *)
(** * Machine part: the barrier on the oracle machines of Idea 16 *)

(** The verifier for [testLangO]: scan right over [x], overwrite the separator
    by [1], scan back to the left end, and query the word [x ++ true :: cert]. *)
Definition testVerifier : OMachine :=
  {| oprogram :=
     [ [obase (halt false); obase (move 0 zero right); obase (move 0 one right);
        obase (move 1 one left)];
       [obase (move 2 blank right); obase (move 1 zero left); obase (move 1 one left);
        obase (halt false)];
       [oquery 3 4; oquery 3 4; oquery 3 4; oquery 3 4];
       [obase (halt true); obase (halt true); obase (halt true); obase (halt true)];
       [obase (halt false); obase (halt false); obase (halt false); obase (halt false)] ] |}.

(** The configuration with state [q], left part [L], and the rest of the tape
    [s] starting at the head. *)
Definition hc (q : nat) (L : list Symbol) (s : list Symbol) : Config :=
  match s with
  | [] => {| state := q; tapeLeft := L; tapeHead := blank; tapeRight := [] |}
  | a :: r => {| state := q; tapeLeft := L; tapeHead := a; tapeRight := r |}
  end.

Theorem moveHead_right : forall q q' L a w r,
  moveHead {| state := q; tapeLeft := L; tapeHead := a; tapeRight := r |} q' w right =
  hc q' (w :: L) r.
Proof. intros q q' L a w r. destruct r; reflexivity. Qed.

(** The left scan target: moving left onto [ys] (nearest symbol first). *)
Definition lc (ys R : list Symbol) : Config :=
  match ys with
  | [] => {| state := 1; tapeLeft := []; tapeHead := blank; tapeRight := R |}
  | a :: rest => {| state := 1; tapeLeft := rest; tapeHead := a; tapeRight := R |}
  end.

Theorem ofBool_ne_sep : forall x, ofBool x <> separator.
Proof. intros [|]; discriminate. Qed.

Lemma ostep_scan_right : forall A x L r,
  ostep A testVerifier (hc 0 L (ofBool x :: r)) = inr (hc 0 (ofBool x :: L) r).
Proof. intros A x L r. destruct x, r; reflexivity. Qed.

Theorem scan_right : forall (A : Oracle) (cs : list Symbol) (t : nat) (b : bool) xs L,
  ORun A testVerifier (hc 0 (rev (map ofBool xs) ++ L) (separator :: cs)) t b ->
  ORun A testVerifier (hc 0 L (map ofBool xs ++ separator :: cs)) (t + length xs) b.
Proof.
  intros A cs t b xs. induction xs as [| x xs IH]; intros L h.
  - rewrite Nat.add_0_r. exact h.
  - simpl (map ofBool (x :: xs) ++ separator :: cs). simpl (length (x :: xs)).
    rewrite Nat.add_succ_r.
    apply orun_next with (hc 0 (ofBool x :: L) (map ofBool xs ++ separator :: cs)).
    + apply ostep_scan_right.
    + apply IH. simpl in h. rewrite <- app_assoc in h. exact h.
Qed.

Lemma ostep_scan_left : forall A y ys R,
  ostep A testVerifier (lc (ofBool y :: ys) R) = inr (lc ys (ofBool y :: R)).
Proof. intros A y ys R. destruct y, ys; reflexivity. Qed.

Theorem scan_left : forall (A : Oracle) (t : nat) (b : bool) ys R,
  ORun A testVerifier {| state := 1; tapeLeft := []; tapeHead := blank;
                         tapeRight := rev (map ofBool ys) ++ R |} t b ->
  ORun A testVerifier (lc (map ofBool ys) R) (t + length ys) b.
Proof.
  intros A t b ys. induction ys as [| y ys IH]; intros R h.
  - rewrite Nat.add_0_r. exact h.
  - simpl (map ofBool (y :: ys)). simpl (length (y :: ys)). rewrite Nat.add_succ_r.
    apply orun_next with (lc (map ofBool ys) (ofBool y :: R)).
    + apply ostep_scan_left.
    + apply IH. simpl in h. rewrite <- app_assoc in h. exact h.
Qed.

Theorem queryWord_bits : forall xs r, queryWord (map ofBool xs ++ r) = xs ++ queryWord r.
Proof.
  intros xs r. induction xs as [| x xs IH]; [reflexivity |].
  destruct x; simpl; rewrite IH; reflexivity.
Qed.

Lemma ostep_sep : forall A L C,
  ostep A testVerifier (hc 0 L (separator :: C)) = inr (lc L (one :: C)).
Proof. intros A L C. destruct L; reflexivity. Qed.

Lemma ostep_query : forall A L a r,
  ostep A testVerifier {| state := 2; tapeLeft := L; tapeHead := a; tapeRight := r |} =
  inr {| state := if A (queryWord (a :: r)) then 3 else 4;
         tapeLeft := L; tapeHead := a; tapeRight := r |}.
Proof. intros A L a r. destruct a; reflexivity. Qed.

(** The explicit run: [2 |x| + 4] steps, answer [A (x ++ true :: cert)]. *)
Theorem testVerifier_run : forall (A : Oracle) (x cert : Word),
  ORun A testVerifier (pairedInput x cert) (2 * length x + 4) (A (x ++ true :: cert)).
Proof.
  intros A x cert.
  set (C := map ofBool cert).
  assert (hq : queryWord (map ofBool x ++ one :: C) = x ++ true :: cert).
  { rewrite queryWord_bits. simpl. unfold C.
    rewrite <- (app_nil_r (map ofBool cert)), queryWord_bits. simpl.
    rewrite app_nil_r. reflexivity. }
  (* final three steps: blank -> right, query, halt *)
  assert (hfin : ORun A testVerifier
            {| state := 1; tapeLeft := []; tapeHead := blank;
               tapeRight := map ofBool x ++ one :: C |} 3 (A (x ++ true :: cert))).
  { destruct (map ofBool x ++ one :: C) as [| a r] eqn:hz.
    - destruct (map ofBool x); discriminate.
    - apply orun_next with {| state := 2; tapeLeft := [blank]; tapeHead := a; tapeRight := r |};
        [reflexivity |].
      apply orun_next with {| state := if A (x ++ true :: cert) then 3 else 4;
                              tapeLeft := [blank]; tapeHead := a; tapeRight := r |}.
      + rewrite ostep_query, hq. reflexivity.
      + apply orun_halt. destruct (A (x ++ true :: cert)), a; reflexivity. }
  assert (h2 : ORun A testVerifier (lc (map ofBool (rev x)) (one :: C))
                 (3 + length (rev x)) (A (x ++ true :: cert))).
  { apply scan_left. rewrite map_rev, rev_involutive. exact hfin. }
  rewrite map_rev in h2.
  assert (h3 : ORun A testVerifier (hc 0 (rev (map ofBool x) ++ []) (separator :: C))
                 (S (3 + length (rev x))) (A (x ++ true :: cert))).
  { apply orun_next with (lc (rev (map ofBool x)) (one :: C)); [| exact h2].
    rewrite app_nil_r. apply ostep_sep. }
  pose proof (scan_right A C _ _ x [] h3) as h4.
  assert (hinit : pairedInput x cert = hc 0 [] (map ofBool x ++ separator :: C)).
  { unfold pairedInput, C. simpl. destruct (map ofBool x); reflexivity. }
  rewrite hinit. rewrite length_rev in h4.
  replace (2 * length x + 4) with (S (3 + length x) + length x) by lia.
  exact h4.
Qed.

(** The BGS-style test language relative to [A]: some extension
    [x ++ true :: y] with [|y| <= |x| + 1] is in [A].  Computable: a bounded
    search over [wordsUpTo] (testLangO_iff gives the meaning). *)
Definition testLangO (A : Oracle) : Language := fun x =>
  existsb (fun y => A (x ++ true :: y)) (wordsUpTo (length x + 1)).

Theorem testLangO_iff : forall A x, testLangO A x = true <->
  exists y : Word, length y <= length x + 1 /\ A (x ++ true :: y) = true.
Proof.
  intros A x. unfold testLangO. split.
  - intro h. apply existsb_exists in h. destruct h as [y [hy hA]].
    exists y. split; [apply mem_wordsUpTo; exact hy | exact hA].
  - intros [y [hy hA]]. apply existsb_exists. exists y.
    split; [apply mem_wordsUpTo; exact hy | exact hA].
Qed.

(** The NP side, in the machine model (proved).  For every oracle [A],
    [testLangO A] is in NP^A, witnessed by the explicit oracle machine
    [testVerifier] making one query.  This is the machine form of
    verifier_one_query. *)
Theorem testLangO_inNPO : forall A : Oracle, InNPO A (testLangO A).
Proof.
  intro A.
  exists (opaired testVerifier), {| coefficient := 4; degree := 1 |},
    {| coefficient := 1; degree := 1 |}. split.
  - intros x cert _. exists (2 * length x + 4), (A (x ++ true :: cert)). split.
    + unfold otimeLimit, evalPoly. simpl. lia.
    + exact (testVerifier_run A x cert).
  - intro x. split.
    + intro h. apply testLangO_iff in h. destruct h as [y [hy hA]].
      exists y, (2 * length x + 4). split; [| split].
      * unfold evalPoly. simpl. lia.
      * unfold otimeLimit, evalPoly. simpl. lia.
      * pose proof (testVerifier_run A x y) as hr. rewrite hA in hr. exact hr.
    + intros [cert [t [hc [_ hr]]]].
      change (ORun A testVerifier (pairedInput x cert) t true) in hr.
      destruct (orun_deterministic _ _ _ _ _ _ _ hr (testVerifier_run A x cert)) as [_ hb].
      apply testLangO_iff. exists cert. split; [| exact (eq_sym hb)].
      unfold evalPoly in hc. simpl in hc. lia.
Qed.

(** Known theorem, not mechanised here (the stage construction of Baker, Gill,
    Solovay, SIAM J. Comput. 4(4), 1975, applied to the test language
    [testLangO]): there is an oracle [B] with [testLangO B] not in P^B.  Its
    query-complexity core is bgs_core. *)
Definition BGSTestSeparation : Prop := exists B : Oracle, ~ InPO B (testLangO B).

(** The test separation gives the BGS separation P^B <> NP^B of the shared
    model. *)
Theorem bgsSeparation_of_testSeparation : BGSTestSeparation -> BGSSeparation.
Proof.
  intros [B hB]. exists B. intro hP. apply hB. apply hP. apply testLangO_inNPO.
Qed.

(** A proof method over machine-oracle statements relativizes if everything
    it proves holds relative to every oracle. *)
Definition MachineRelativizing (Proves : (Oracle -> Prop) -> Prop) : Prop :=
  forall S, Proves S -> forall A, S A.

(** BGS barrier for machine statements.  Under the known BGS theorems, a
    relativizing method proves neither P^A = NP^A nor P^A <> NP^A as
    statements about all oracles. *)
Theorem machineRelativizing_cannot_settle : forall (Proves : (Oracle -> Prop) -> Prop),
  MachineRelativizing Proves -> BGSCollapse -> BGSTestSeparation ->
  ~ Proves PEqualsNPO /\ ~ Proves (fun A => ~ PEqualsNPO A).
Proof.
  intros Proves hrel h1 h2.
  destruct h1 as [A hA].
  destruct (bgsSeparation_of_testSeparation h2) as [B hB]. split.
  - intro h. exact (hB (hrel _ h B)).
  - intro h. exact (hrel _ h A hA).
Qed.
