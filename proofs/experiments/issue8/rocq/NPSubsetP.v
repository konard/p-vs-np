(** * Issue 8: the target NP ⊆ P and a verified DPLL search, over the shared model

    The Rocq twin of [proofs/experiments/issue8/lean/NPSubsetP.lean], with the
    same statement names.  It states NP ⊆ P over [Complexity], relates it to
    the class equality and to SAT, and proves a concrete DPLL search correct
    for the shared [SAT] language, with a call-count bound.  It does not prove
    NP ⊆ P.  The call count of [dpll] is not a count of [Run] steps; the
    bridge [npSubsetP_of_dpll_machine] names what is missing: a [Machine]
    computing [dpllSAT] in polynomially many [Run] steps, and [SATHard],
    which stays an explicit premise.  Nothing is assumed as an axiom. *)

From Stdlib Require Import Arith PeanoNat Lia Bool List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines SATVerifier Idea41.
From proofs.experiments.issue609.rocq Require Import PEqualsNPAttempt.

(** ** The target: NP ⊆ P *)

Definition NPSubsetP : Prop := forall L : Language, InNP L -> InP L.

(** The shared statement [PEqualsNP] is literally NP ⊆ P. *)
Theorem npSubsetP_iff_pEqualsNP : NPSubsetP <-> PEqualsNP.
Proof. reflexivity. Qed.

(** Because P ⊆ NP is proved, NP ⊆ P says exactly that the classes are equal. *)
Theorem npSubsetP_iff_classes_equal :
  NPSubsetP <-> forall L : Language, InP L <-> InNP L.
Proof.
  split.
  - intros h L. split; [apply pSubsetNP | apply h].
  - intros h L hL. apply (h L). exact hL.
Qed.

(** With the named hardness premise, NP ⊆ P is the single statement SAT ∈ P. *)
Theorem npSubsetP_iff_inP_sat : SATHard -> (NPSubsetP <-> InP SAT).
Proof. intro hard. symmetry. exact (inP_sat_iff_of_hard hard). Qed.

(** With the named hardness premise, NP ⊆ P is the existence of a
    polynomial-time SAT machine ([Candidate] from issue 609). *)
Theorem npSubsetP_iff_candidate : SATHard -> (NPSubsetP <-> exists c : Candidate, True).
Proof. intro hard. symmetry. exact (candidate_iff_pEqualsNP hard). Qed.

(** ** The PR #41 DPLL regression in the shared SAT semantics

    [(¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x1 ∨ ¬x3) ∧ (x1 ∨ ¬x2) ∧ (x1 ∨ x3)], with
    [x1, x2, x3] as variables [0, 1, 2].  PR #41's Python solver answered
    UNSAT (issue #610). *)

Definition issue610Formula : CNF :=
  [[mkLit 0 false; mkLit 1 true]; [mkLit 1 false; mkLit 2 true];
   [mkLit 0 false; mkLit 2 false]; [mkLit 0 true; mkLit 1 false];
   [mkLit 0 true; mkLit 2 true]].

(** [x1 = false, x2 = false, x3 = true] satisfies every clause. *)
Theorem issue610_satisfiable : Satisfiable issue610Formula.
Proof. exists (fun i => Nat.eqb i 2). reflexivity. Qed.

Theorem issue610_sat : SAT (encodeCNF issue610Formula) = true.
Proof. apply sat_encode. exact issue610_satisfiable. Qed.

(** ** Conditioning a formula on one variable *)

(** The assignment [a] with variable [v] set to [b]. *)
Definition upd (a : Assignment) (v : nat) (b : bool) : Assignment :=
  fun i => if Nat.eqb i v then b else a i.

(** [c] contains the literal [(v, b)]. *)
Fixpoint hasLit (v : nat) (b : bool) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' => (Nat.eqb (var l) v && Bool.eqb (pos l) b) || hasLit v b c'
  end.

(** Delete the literals of variable [v]. *)
Fixpoint dropVar (v : nat) (c : Clause) : Clause :=
  match c with
  | [] => []
  | l :: c' => if Nat.eqb (var l) v then dropVar v c' else l :: dropVar v c'
  end.

(** Condition on [x_v = b]: satisfied clauses go, false literals are deleted. *)
Fixpoint assign (v : nat) (b : bool) (phi : CNF) : CNF :=
  match phi with
  | [] => []
  | c :: phi' => if hasLit v b c then assign v b phi' else dropVar v c :: assign v b phi'
  end.

Lemma evalLit_upd : forall a v b l,
  evalLit (upd a v b) l = if Nat.eqb (var l) v then Bool.eqb b (pos l) else evalLit a l.
Proof. intros a v b l. unfold evalLit, upd. destruct (Nat.eqb (var l) v); reflexivity. Qed.

Lemma evalClause_hasLit : forall a v b c,
  hasLit v b c = true -> evalClause (upd a v b) c = true.
Proof.
  intros a v b c. induction c as [|l c IH]; simpl; intro h; [discriminate|].
  apply orb_true_iff in h. destruct h as [h|h].
  - apply andb_true_iff in h. destruct h as [hv hb].
    rewrite evalLit_upd, hv. apply eqb_prop in hb. rewrite hb, eqb_reflx. reflexivity.
  - rewrite (IH h). apply orb_true_r.
Qed.

Lemma evalClause_dropVar : forall a v b c, hasLit v b c = false ->
  evalClause (upd a v b) c = evalClause a (dropVar v c).
Proof.
  intros a v b c. induction c as [|l c IH]; simpl; intro h; [reflexivity|].
  apply orb_false_iff in h. destruct h as [hl hc].
  rewrite evalLit_upd. destruct (Nat.eqb (var l) v) eqn:hv; simpl in hl.
  - replace (Bool.eqb b (pos l)) with false.
    + exact (IH hc).
    + destruct b, (pos l); simpl in *; congruence.
  - simpl. rewrite (IH hc). reflexivity.
Qed.

(** Conditioning is evaluation under the updated assignment. *)
Lemma evalCNF_assign : forall a v b phi,
  evalCNF a (assign v b phi) = evalCNF (upd a v b) phi.
Proof.
  intros a v b phi. induction phi as [|c phi IH]; simpl; [reflexivity|].
  destruct (hasLit v b c) eqn:hc.
  - rewrite IH, (evalClause_hasLit a v b c hc). reflexivity.
  - simpl. rewrite IH, (evalClause_dropVar a v b c hc). reflexivity.
Qed.

Lemma evalCNF_ext : forall a a' phi, (forall i, a i = a' i) ->
  evalCNF a phi = evalCNF a' phi.
Proof.
  intros a a' phi h. induction phi as [|c phi IH]; simpl; [reflexivity|].
  rewrite IH. f_equal. induction c as [|l c IHc]; simpl; [reflexivity|].
  unfold evalLit. rewrite h, IHc. reflexivity.
Qed.

Lemma upd_self : forall a v i, upd a v (a v) i = a i.
Proof.
  intros a v i. unfold upd. destruct (Nat.eqb_spec i v); [subst; reflexivity | reflexivity].
Qed.

Lemma satisfiable_of_assign : forall v b phi,
  Satisfiable (assign v b phi) -> Satisfiable phi.
Proof. intros v b phi [a ha]. exists (upd a v b). rewrite <- evalCNF_assign. exact ha. Qed.

Lemma assign_satisfiable : forall a v phi,
  evalCNF a phi = true -> Satisfiable (assign v (a v) phi).
Proof.
  intros a v phi ha. exists a. rewrite evalCNF_assign.
  rewrite (evalCNF_ext _ a phi (upd_self a v)). exact ha.
Qed.

(** Splitting on [x_v]. *)
Lemma satisfiable_split : forall v phi,
  Satisfiable phi <-> Satisfiable (assign v true phi) \/ Satisfiable (assign v false phi).
Proof.
  intros v phi. split.
  - intros [a ha]. pose proof (assign_satisfiable a v phi ha) as h.
    revert h. destruct (a v); intro h; [left | right]; exact h.
  - intros [h|h]; exact (satisfiable_of_assign _ _ _ h).
Qed.

Lemma evalCNF_true_iff : forall a phi,
  evalCNF a phi = true <-> forall c, In c phi -> evalClause a c = true.
Proof.
  intros a phi. induction phi as [|c phi IH]; simpl.
  - split; [intros _ c [] | reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [h1 h2] c' [e|h]; [subst; exact h1 | exact (h2 c' h)].
    + intro h. split; [apply h; left; reflexivity | intros c' h'; apply h; right; exact h'].
Qed.

(** ** Unit clauses and conflicts *)

(** The literal of the first unit clause, if any. *)
Fixpoint unitLit (phi : CNF) : option Lit :=
  match phi with
  | [] => None
  | [l] :: _ => Some l
  | _ :: phi' => unitLit phi'
  end.

(** Some clause is empty. *)
Fixpoint hasEmpty (phi : CNF) : bool :=
  match phi with
  | [] => false
  | [] :: _ => true
  | _ :: phi' => hasEmpty phi'
  end.

Lemma unitLit_mem : forall phi l, unitLit phi = Some l -> In [l] phi.
Proof.
  induction phi as [|c phi IH]; intros l h; [discriminate|].
  destruct c as [|l1 [|l2 c]]; cbn in h.
  - right. exact (IH l h).
  - left. injection h as <-. reflexivity.
  - right. exact (IH l h).
Qed.

Lemma hasEmpty_mem : forall phi, hasEmpty phi = true -> In [] phi.
Proof.
  induction phi as [|c phi IH]; intro h; [discriminate|].
  destruct c as [|l c]; [left; reflexivity | right; exact (IH h)].
Qed.

Lemma not_satisfiable_of_empty : forall phi, In [] phi -> ~ Satisfiable phi.
Proof.
  intros phi h [a ha]. rewrite evalCNF_true_iff in ha.
  specialize (ha [] h). discriminate.
Qed.

(** A unit clause [[l]] forces its literal. *)
Lemma satisfiable_unit : forall phi l, In [l] phi ->
  (Satisfiable phi <-> Satisfiable (assign (var l) (pos l) phi)).
Proof.
  intros phi l h. split.
  - intros [a ha]. pose proof (proj1 (evalCNF_true_iff a phi) ha [l] h) as hl.
    simpl in hl. rewrite orb_false_r in hl. unfold evalLit in hl. apply eqb_prop in hl.
    rewrite <- hl. exact (assign_satisfiable a (var l) phi ha).
  - apply satisfiable_of_assign.
Qed.

(** ** The DPLL search

    [k] is fuel: every call conditions on one variable, and [k] bounds the
    number of distinct variables left. *)

Fixpoint dpll (k : nat) (phi : CNF) : bool :=
  match k with
  | 0 => match phi with [] => true | _ => false end
  | S k' =>
    match phi with
    | [] => true
    | c :: _ =>
      if hasEmpty phi then false else
      match unitLit phi with
      | Some l => dpll k' (assign (var l) (pos l) phi)
      | None =>
        match c with
        | [] => false
        | l :: _ => dpll k' (assign (var l) true phi) || dpll k' (assign (var l) false phi)
        end
      end
    end
  end.

(** Every variable of [phi] is listed in [vs]. *)
Definition VarsIn (vs : list nat) (phi : CNF) : Prop :=
  forall c, In c phi -> forall l, In l c -> In (var l) vs.

Lemma mem_dropVar : forall v l c, In l (dropVar v c) -> In l c /\ var l <> v.
Proof.
  intros v l c. induction c as [|l' c IH]; simpl; [intros []|].
  destruct (Nat.eqb (var l') v) eqn:hv; intro h.
  - destruct (IH h) as [h1 h2]. split; [right; exact h1 | exact h2].
  - destruct h as [e|h].
    + subst l'. split; [left; reflexivity | apply Nat.eqb_neq; exact hv].
    + destruct (IH h) as [h1 h2]. split; [right; exact h1 | exact h2].
Qed.

Lemma mem_assign : forall v b c' phi, In c' (assign v b phi) ->
  exists c, In c phi /\ c' = dropVar v c.
Proof.
  intros v b c' phi. induction phi as [|c phi IH]; simpl; [intros []|].
  destruct (hasLit v b c); intro h.
  - destruct (IH h) as [d [hd e]]. exists d. split; [right; exact hd | exact e].
  - destruct h as [e|h].
    + exists c. split; [left; reflexivity | symmetry; exact e].
    + destruct (IH h) as [d [hd e]]. exists d. split; [right; exact hd | exact e].
Qed.

(** Conditioning on a listed variable removes it from the list. *)
Lemma varsIn_assign : forall vs phi v b, VarsIn vs phi ->
  VarsIn (remove Nat.eq_dec v vs) (assign v b phi).
Proof.
  intros vs phi v b h c' hc' l hl.
  destruct (mem_assign v b c' phi hc') as [c [hc e]]. subst c'.
  destruct (mem_dropVar v l c hl) as [hlc hlv].
  apply in_in_remove; [exact hlv | exact (h c hc l hlc)].
Qed.

Lemma length_remove_le : forall vs v k, In v vs -> length vs <= S k ->
  length (remove Nat.eq_dec v vs) <= k.
Proof. intros vs v k hv hk. pose proof (remove_length_lt Nat.eq_dec vs v hv). lia. Qed.

(** [dpll] is correct whenever the fuel bounds the variables. *)
Theorem dpll_correct : forall k phi vs, VarsIn vs phi -> length vs <= k ->
  (dpll k phi = true <-> Satisfiable phi).
Proof.
  induction k as [|k IH]; intros phi vs hvs hk.
  - destruct phi as [|c phi]; simpl.
    + split; [intros _; exists (fun _ => false); reflexivity | reflexivity].
    + destruct vs; [|simpl in hk; lia].
      destruct c as [|l c].
      * split; [discriminate |].
        intro h. exfalso. exact (not_satisfiable_of_empty ([] :: phi) (or_introl eq_refl) h).
      * exfalso. exact (hvs (l :: c) (or_introl eq_refl) l (or_introl eq_refl)).
  - destruct phi as [|c phi].
    + simpl. split; [intros _; exists (fun _ => false); reflexivity | reflexivity].
    + cbn [dpll]. destruct (hasEmpty (c :: phi)) eqn:he.
      * split; [discriminate |].
        intro h. exfalso. exact (not_satisfiable_of_empty _ (hasEmpty_mem _ he) h).
      * destruct (unitLit (c :: phi)) as [l|] eqn:hu.
        -- pose proof (unitLit_mem _ _ hu) as hmem.
           assert (hv : In (var l) vs) by exact (hvs [l] hmem l (or_introl eq_refl)).
           rewrite (satisfiable_unit _ _ hmem).
           apply (IH _ (remove Nat.eq_dec (var l) vs));
             [apply varsIn_assign; exact hvs | exact (length_remove_le _ _ _ hv hk)].
        -- destruct c as [|l c]; [simpl in he; discriminate |].
           assert (hv : In (var l) vs) by exact (hvs (l :: c) (or_introl eq_refl) l (or_introl eq_refl)).
           rewrite orb_true_iff, (satisfiable_split (var l)).
           rewrite (IH _ _ (varsIn_assign _ _ (var l) true hvs) (length_remove_le _ _ _ hv hk)).
           rewrite (IH _ _ (varsIn_assign _ _ (var l) false hvs) (length_remove_le _ _ _ hv hk)).
           reflexivity.
Qed.

(** ** [dpll] decides the shared SAT language *)

(** Run [dpll] on the decoded formula with the input length as fuel. *)
Definition dpllSAT : Language := fun w => dpll (length w) (decode w).

Lemma varsIn_seq : forall n phi, VarsBelow n phi -> VarsIn (seq 0 n) phi.
Proof. intros n phi h c hc l hl. apply in_seq. specialize (h c hc l hl). lia. Qed.

Theorem dpllSAT_iff : forall w, dpllSAT w = true <-> Satisfiable (decode w).
Proof.
  intro w. apply (dpll_correct _ _ (seq 0 (length w))).
  - apply varsIn_seq, varsBelow_decode.
  - rewrite length_seq. lia.
Qed.

(** The concrete solver agrees with [SAT] on every word, including words that
    are not encodings. *)
Theorem dpllSAT_eq_SAT : forall w, dpllSAT w = SAT w.
Proof. intro w. apply eq_true_iff_eq. rewrite dpllSAT_iff, sat_iff. reflexivity. Qed.

(** On encodings the answer is satisfiability of the formula. *)
Theorem dpllSAT_encode : forall phi, dpllSAT (encodeCNF phi) = true <-> Satisfiable phi.
Proof. intro phi. rewrite dpllSAT_eq_SAT. apply sat_encode. Qed.

(** Regression tests: the issue #610 formula is accepted, and the formula with
    one empty clause is rejected. *)
Theorem dpllSAT_issue610 : dpllSAT (encodeCNF issue610Formula) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem dpllSAT_empty_clause : dpllSAT (encodeCNF [[]]) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The call count

    [dpllCalls] counts the calls [dpll] makes, including the short-circuit of
    [||]: the [false] branch is searched only after the [true] branch fails. *)

Fixpoint dpllCalls (k : nat) (phi : CNF) : nat :=
  match k with
  | 0 => 1
  | S k' =>
    match phi with
    | [] => 1
    | c :: _ =>
      if hasEmpty phi then 1 else
      match unitLit phi with
      | Some l => 1 + dpllCalls k' (assign (var l) (pos l) phi)
      | None =>
        match c with
        | [] => 1
        | l :: _ =>
          if dpll k' (assign (var l) true phi)
          then 1 + dpllCalls k' (assign (var l) true phi)
          else 1 + dpllCalls k' (assign (var l) true phi) +
                 dpllCalls k' (assign (var l) false phi)
        end
      end
    end
  end.

(** The search tree has fewer than [2^(k+1)] nodes. *)
Theorem dpllCalls_lt : forall k phi, dpllCalls k phi < 2 ^ (k + 1).
Proof.
  intros k phi. rewrite Nat.add_1_r. revert phi.
  induction k as [|k IH]; intro phi; [simpl; lia |].
  pose proof (Nat.pow_succ_r' 2 (S k)) as hp.
  pose proof (Nat.pow_nonzero 2 (S k) ltac:(lia)) as hz.
  destruct phi as [|c phi]; [cbn [dpllCalls]; lia |].
  cbn [dpllCalls]. destruct (hasEmpty (c :: phi)); [lia |].
  destruct (unitLit (c :: phi)) as [l|].
  - pose proof (IH (assign (var l) (pos l) (c :: phi))). lia.
  - destruct c as [|l c]; [lia |].
    pose proof (IH (assign (var l) true (@cons Clause (l :: c) phi))).
    pose proof (IH (assign (var l) false (@cons Clause (l :: c) phi))).
    destruct (dpll k (assign (var l) true (@cons Clause (l :: c) phi))); lia.
Qed.

(** On input [w], the solver makes fewer than [2^(|w|+1)] calls. *)
Theorem dpllSAT_calls_le : forall w, dpllCalls (length w) (decode w) < 2 ^ (length w + 1).
Proof. intro w. apply dpllCalls_lt. Qed.

(** The proved bound is not polynomial.  This only says that the bound above
    does not give a polynomial-time algorithm; it is not a lower bound for SAT. *)
Theorem calls_bound_not_polynomial : ~ PolynomiallyBounded (fun n => 2 ^ (n + 1)).
Proof.
  intros [a [k h]].
  destruct (poly_le_two_pow (a + 1) k) as [N hN].
  specialize (h N). specialize (hN N (le_n N)). cbv beta in h.
  replace (2 ^ (N + 1)) with (2 * 2 ^ N) in h by (rewrite Nat.add_1_r; reflexivity).
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l in hN.
  pose proof (Nat.pow_nonzero (N + 1) k ltac:(lia)).
  lia.
Qed.

(** ** The bridge to NP ⊆ P

    The remaining obligations are named: a machine computing [dpllSAT] within
    a polynomial number of [Run] steps, and [SATHard]. *)

(** A polynomial-time machine for [dpllSAT] is a [Candidate]. *)
Theorem candidate_of_dpll_machine : forall m p,
  DecidesWithin m p dpllSAT -> exists c : Candidate, True.
Proof.
  intros m p h. apply candidate_of_inP. apply (inP_of_decidesWithin m p).
  intro x. destruct (h x) as [t [b [ht [hr hb]]]].
  exists t, b. split; [exact ht | split; [exact hr |]].
  rewrite hb. apply dpllSAT_eq_SAT.
Qed.

(** With [SATHard], such a machine proves NP ⊆ P. *)
Theorem npSubsetP_of_dpll_machine : SATHard -> forall m p,
  DecidesWithin m p dpllSAT -> NPSubsetP.
Proof.
  intros hard m p h. destruct (candidate_of_dpll_machine m p h) as [c _].
  exact (pEqualsNP_of_candidate hard c).
Qed.

(** Conversely, NP ⊆ P yields such a machine; no [SATHard] is needed here. *)
Theorem dpll_machine_of_npSubsetP : NPSubsetP ->
  exists m p, DecidesWithin m p dpllSAT.
Proof.
  intro h. pose proof (inP_sat_of_pEqualsNP satInNP h) as hs.
  apply polyDec_iff_inP in hs. destruct hs as [m [p hm]].
  exists m, p. intro x. destruct (hm x) as [t [b [ht [hr hb]]]].
  exists t, b. split; [exact ht | split; [exact hr |]].
  rewrite hb. symmetry. apply dpllSAT_eq_SAT.
Qed.
