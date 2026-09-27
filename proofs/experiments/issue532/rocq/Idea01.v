(** * Issue #532, Idea 01 -- Exact SAT algorithm (brute force as the baseline)

    Rocq counterpart of [lean/Idea01.lean]; theorem names are aligned.  The
    file works in the shared machine model [Machines.v] (finite-table
    single-tape Turing machines, [InP], [PolyReduces], and the language [SAT]
    of encoded CNFs).  The CNF syntax, [bruteForce], [bruteForce_correct],
    [allAssignments], [mem_allAssignments_iff] and the lossless encoding
    [encodeCNF] ([decode_encode], [encode_injective]) come from that shared
    layer.

    Proved for every CNF and every [n]:
    - [length_allAssignments], [nodup_allAssignments]: the enumeration has
      exactly 2^n entries, without repetition;
    - [bruteForceCost_le], [bruteForceCost_unsat], [hardFamily_cost]: at most
      2^n formula evaluations, exactly 2^n on every unsatisfiable formula, and
      an unsatisfiable family with exactly n variables for every n >= 1;
    - [numVars_le_encodingLength], [bruteForceCost_le_exp_size]: the cost is at
      most 2^(input length) for the binary encoding [encodeCNF];
    - the open obligation [PolySATDecider := InP SAT] and its conditional
      theorems [polySATDecider_iff_polyDec], [pEqualsNP_of_polySATDecider]
      (under [SATHard]), [polySATDecider_of_pEqualsNP] (under [SATInNP]),
      [polySATDecider_iff] (under [CookLevin]),
      [pNotEqualsNP_of_not_polySATDecider] and
      [polySAT_agrees_with_bruteForce];
    - [polySATDecider_not_trivial]: [InP] is not satisfied by every language.

    The Cook-Levin theorem is not mechanised; it enters only as the explicit
    premises [SATHard], [SATInNP] or [CookLevin] of the shared layer.  No
    axioms are used.

    Verdict: brute force is refuted as a polynomial-time algorithm; the route
    "a uniform polynomial-time SAT decider" is [InP SAT], which under
    Cook-Levin is equivalent to P = NP and remains open.  [PolySATDecider] is
    a definition, never postulated. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(** ** The enumeration of assignments *)

(** The enumeration has exactly [2^n] entries. *)
Theorem length_allAssignments (n : nat) : length (allAssignments n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Lemma nodup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 H; simpl; auto.
  inversion H1; subst. constructor.
  - intros Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + contradiction.
    + apply (H x); simpl; auto.
  - apply IH; auto. intros y Hy; apply H; simpl; auto.
Qed.

Lemma nodup_map_cons (b : bool) (L : list (list bool)) :
  NoDup L -> NoDup (map (cons b) L).
Proof.
  induction L as [|x L IH]; intros H; simpl; constructor.
  - inversion H; subst. intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hin]]; injection Hy; intros; subst; contradiction.
  - inversion H; subst; auto.
Qed.

Theorem nodup_allAssignments (n : nat) : NoDup (allAssignments n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; auto | constructor].
  - apply nodup_app_intro; try apply nodup_map_cons; auto.
    intros x Hx Hy; apply in_map_iff in Hx; apply in_map_iff in Hy.
    destruct Hx as [u [Hu _]]; destruct Hy as [w [Hw _]]; subst.
    discriminate.
Qed.

Lemma clauseBound_cons (l : Lit) (c : Clause) :
  clauseBound (l :: c) = Nat.max (S (var l)) (clauseBound c).
Proof. reflexivity. Qed.

Lemma numVars_cons (c : Clause) (phi : CNF) :
  numVars (c :: phi) = Nat.max (clauseBound c) (numVars phi).
Proof. reflexivity. Qed.

(** ** Cost: number of formula evaluations *)

Fixpoint searchCount (phi : CNF) (L : list (list bool)) : nat :=
  match L with
  | [] => 0
  | v :: vs => if evalCNF (toAssign v) phi then 1 else 1 + searchCount phi vs
  end.

Definition bruteForceCost (n : nat) (phi : CNF) : nat := searchCount phi (allAssignments n).

Lemma searchCount_le (phi : CNF) (L : list (list bool)) : searchCount phi L <= length L.
Proof.
  induction L as [|v L IH]; simpl; auto.
  destruct (evalCNF (toAssign v) phi); lia.
Qed.

Lemma searchCount_all_false (phi : CNF) (L : list (list bool)) :
  (forall v, In v L -> evalCNF (toAssign v) phi = false) -> searchCount phi L = length L.
Proof.
  induction L as [|v L IH]; intros H; simpl; auto.
  rewrite (H v (or_introl eq_refl)), IH; auto.
  intros w Hw; apply H; simpl; auto.
Qed.

Theorem bruteForceCost_le (n : nat) (phi : CNF) : bruteForceCost n phi <= 2 ^ n.
Proof.
  unfold bruteForceCost; rewrite <- length_allAssignments; apply searchCount_le.
Qed.

Theorem bruteForceCost_unsat (n : nat) (phi : CNF) :
  ~ Satisfiable phi -> bruteForceCost n phi = 2 ^ n.
Proof.
  intros H; unfold bruteForceCost; rewrite searchCount_all_false, length_allAssignments; auto.
  intros v _; destruct (evalCNF (toAssign v) phi) eqn:Hv; auto.
  exfalso; apply H; exists (toAssign v); auto.
Qed.

Fixpoint tautChain (k : nat) : CNF :=
  match k with
  | 0 => []
  | S k' => [mkLit k' true; mkLit k' false] :: tautChain k'
  end.

Definition hardFamily (n : nat) : CNF :=
  [mkLit 0 true] :: [mkLit 0 false] :: tautChain n.

Lemma numVars_tautChain (k : nat) : numVars (tautChain k) = k.
Proof.
  induction k as [|k IH]; auto.
  change (numVars (tautChain (S k))) with
    (Nat.max (Nat.max (S k) (Nat.max (S k) 0)) (numVars (tautChain k))).
  rewrite IH; lia.
Qed.

Theorem hardFamily_unsat (n : nat) : ~ Satisfiable (hardFamily n).
Proof.
  intros [a Ha]; unfold hardFamily in Ha; simpl in Ha; unfold evalLit in Ha; simpl in Ha.
  destruct (a 0); simpl in Ha; discriminate.
Qed.

Theorem hardFamily_cost (n : nat) : 1 <= n ->
  numVars (hardFamily n) = n /\ ~ Satisfiable (hardFamily n) /\
  bruteForceCost (numVars (hardFamily n)) (hardFamily n) = 2 ^ n.
Proof.
  intros Hn.
  assert (Hv : numVars (hardFamily n) = n).
  { change (numVars (hardFamily n)) with
      (Nat.max (Nat.max 1 0) (Nat.max (Nat.max 1 0) (numVars (tautChain n)))).
    rewrite numVars_tautChain; lia. }
  split; [auto|split; [apply hardFamily_unsat|]].
  rewrite Hv; apply bruteForceCost_unsat, hardFamily_unsat.
Qed.

(** ** Encoding length *)

Lemma length_ticks (v : nat) : length (ticks v) = 2 * v.
Proof. induction v as [|v IH]; simpl; auto. rewrite IH; lia. Qed.

Lemma clauseBound_le_length (c : Clause) : clauseBound c <= length (encodeClause c).
Proof.
  induction c as [|l c IH]; [simpl; auto|].
  rewrite clauseBound_cons; simpl encodeClause.
  unfold encodeLit; rewrite !length_app, length_ticks; simpl length; lia.
Qed.

Theorem numVars_le_encodingLength (phi : CNF) : numVars phi <= length (encodeCNF phi).
Proof.
  induction phi as [|c phi IH]; auto.
  rewrite numVars_cons; simpl encodeCNF.
  rewrite length_app; pose proof (clauseBound_le_length c); lia.
Qed.

Theorem bruteForceCost_le_exp_size (phi : CNF) :
  bruteForceCost (numVars phi) phi <= 2 ^ length (encodeCNF phi).
Proof.
  eapply Nat.le_trans; [apply bruteForceCost_le|].
  apply Nat.pow_le_mono_r; [lia|apply numVars_le_encodingLength].
Qed.

(** ** The open obligation, in the shared machine model *)

(** Open obligation: a polynomial-time finite-table machine decides the
    shared language [SAT] of encoded CNFs.  Under Cook-Levin (not mechanised)
    it is equivalent to P = NP.  It is a definition and is never postulated. *)
Definition PolySATDecider : Prop := InP SAT.

Theorem polySATDecider_iff_polyDec : PolySATDecider <-> PolyDec SAT.
Proof. symmetry. apply polyDec_iff_inP. Qed.

(** Conditional theorem: under the named premise [SATHard] (the hardness half
    of Cook-Levin, not mechanised here) the obligation implies P = NP. *)
Theorem pEqualsNP_of_polySATDecider (hard : SATHard) (h : PolySATDecider) : PEqualsNP.
Proof. exact (pEqualsNP_of_inP_sat hard h). Qed.

(** Conversely, under the named premise [SATInNP], P = NP implies the
    obligation. *)
Theorem polySATDecider_of_pEqualsNP (mem : SATInNP) (h : PEqualsNP) : PolySATDecider.
Proof. exact (inP_sat_of_pEqualsNP mem h). Qed.

(** Under the named premise [CookLevin] the obligation is exactly P = NP. *)
Theorem polySATDecider_iff (hCL : CookLevin) : PolySATDecider <-> PEqualsNP.
Proof. exact (inP_sat_iff hCL). Qed.

(** Refuting the obligation would separate P from NP (given [SATInNP]). *)
Theorem pNotEqualsNP_of_not_polySATDecider (mem : SATInNP) (h : ~ PolySATDecider) :
  PNotEqualsNP.
Proof. intro hp. exact (h (polySATDecider_of_pEqualsNP mem hp)). Qed.

(** Conditional theorem: a machine witnessing the obligation outputs, within
    its polynomial budget, exactly the brute-force answer on the encoding of
    every CNF. *)
Theorem polySAT_agrees_with_bruteForce :
  PolySATDecider ->
  exists (M : Machine) (p : Polynomial), forall phi : CNF, exists t,
    t <= evalPoly p (length (encodeCNF phi)) /\
    Run M (initial (encodeCNF phi)) t (bruteForce (numVars phi) phi).
Proof.
  intros h. destruct (inP_sat_on_encodings h) as [M [p HM]].
  exists M, p; intros phi.
  destruct (HM phi) as [t [b [Ht [Hr Hb]]]]; exists t; split; auto.
  replace (bruteForce (numVars phi) phi) with b; auto.
  pose proof (bruteForce_correct phi) as Hbf.
  destruct b, (bruteForce (numVars phi) phi) eqn:E; auto.
  - exfalso. assert (Hs : Satisfiable phi) by (apply Hb; auto).
    apply Hbf in Hs; congruence.
  - exfalso. assert (Hs : Satisfiable phi) by (apply Hbf; auto).
    apply Hb in Hs; discriminate.
Qed.

(** Non-vacuity: [InP] is not satisfied by every language (the shared
    diagonal language [Diag] is not in P), so [PolySATDecider] is a genuine
    constraint on [SAT] rather than a tautology. *)
Theorem polySATDecider_not_trivial : ~ (forall L : Language, InP L).
Proof. intro h. exact (diag_not_inP (h Diag)). Qed.
