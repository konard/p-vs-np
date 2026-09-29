(** * Issue #532, Idea 04 -- Local consistency does not imply global satisfiability

    Rocq counterpart of [lean/Idea04.lean]; theorem names are aligned.

    A system is a list of pairs [(i, j)], read as [x_i <> x_j] over booleans.
    [cycle n] is [x_i <> x_((i+1) mod n)] for [i < n].

    - [cycle_even_sat], [cycle_odd_unsat], [cycle_sat_iff]: the cycle is
      satisfiable iff [n mod 2 = 0];
    - [missing_constraint_sat], [short_subsystem_sat]: every subsystem that
      misses a constraint (in particular every subsystem with fewer than [n]
      constraints) is satisfiable;
    - [odd_cycle_locally_consistent], [local_consistency_insufficient],
      [no_local_to_global]: for every [k] there is a [k]-locally consistent
      unsatisfiable system;
    - [sysCNF_iff], [cycleCNF_sat_iff]: the same systems as 2-CNF formulas.

    Verdict: checking bounded-size pieces never certifies global
    satisfiability. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Ltac mod2 x := pose proof (Nat.div_mod_eq x 2); pose proof (Nat.mod_upper_bound x 2 ltac:(lia)).

(** ** Disequality systems *)

Definition System := list (nat * nat).

Definition Solves (x : nat -> bool) (sys : System) : Prop :=
  forall p, In p sys -> x (fst p) <> x (snd p).

Definition SatSys (sys : System) : Prop := exists x : nat -> bool, Solves x sys.

Definition cycle (n : nat) : System := map (fun i => (i, (S i) mod n)) (seq 0 n).

Lemma mem_cycle (n : nat) (p : nat * nat) :
  In p (cycle n) <-> exists i, i < n /\ p = (i, (S i) mod n).
Proof.
  unfold cycle; rewrite in_map_iff; split.
  - intros [i [Hp Hi]]; apply in_seq in Hi; exists i; split; [lia|auto].
  - intros [i [Hi Hp]]; exists i; split; auto; apply in_seq; lia.
Qed.

Definition par (i : nat) : bool := Nat.eqb (i mod 2) 1.

Lemma par_succ (i : nat) : par (S i) = negb (par i).
Proof.
  unfold par. mod2 i. mod2 (S i).
  destruct (Nat.eq_dec (i mod 2) 0) as [Hz|Hz].
  - replace (S i mod 2) with 1 by lia. rewrite Hz; reflexivity.
  - replace (S i mod 2) with 0 by lia. replace (i mod 2) with 1 by lia; reflexivity.
Qed.

Lemma par_ne_succ (i : nat) : par i <> par (S i).
Proof. rewrite par_succ; destruct (par i); discriminate. Qed.

Lemma par_eq_false_iff (i : nat) : par i = false <-> i mod 2 = 0.
Proof.
  unfold par. mod2 i. rewrite Nat.eqb_neq. lia.
Qed.

Lemma succ_mod_of_lt (i n : nat) : S i < n -> (S i) mod n = S i.
Proof. apply Nat.mod_small. Qed.

Lemma succ_mod_of_eq (i n : nat) : S i = n -> (S i) mod n = 0.
Proof. intros H; rewrite H; apply Nat.Div0.mod_same. Qed.

(** ** Even cycles are satisfiable, odd cycles are not *)

Theorem cycle_even_sat (n : nat) : n mod 2 = 0 -> SatSys (cycle n).
Proof.
  intros Hn; exists par; intros p Hp.
  apply mem_cycle in Hp; destruct Hp as [i [Hi Hp]]; subst p; simpl.
  destruct (Nat.lt_ge_cases (S i) n) as [Hlt|Hge].
  - rewrite succ_mod_of_lt by auto; apply par_ne_succ.
  - rewrite succ_mod_of_eq by lia.
    assert (Hpi : par i = true).
    { destruct (par i) eqn:E; auto. apply par_eq_false_iff in E.
      mod2 i; mod2 n; lia. }
    rewrite Hpi; discriminate.
Qed.

Lemma solution_alternates (n : nat) (x : nat -> bool) :
  Solves x (cycle n) -> forall i, i < n -> (x i = x 0 <-> i mod 2 = 0).
Proof.
  intros Hx i; induction i as [|i IH]; intros Hi.
  - split; auto.
  - assert (Hc : x i <> x (S i)).
    { assert (Hm : In (i, (S i) mod n) (cycle n)) by (apply mem_cycle; exists i; split; [lia|auto]).
      pose proof (Hx _ Hm) as H.
      simpl in H. rewrite succ_mod_of_lt in H by auto. exact H. }
    specialize (IH ltac:(lia)).
    assert (Hpar : (S i) mod 2 = 0 <-> ~ i mod 2 = 0) by (mod2 i; mod2 (S i); lia).
    rewrite Hpar. destruct (x i), (x (S i)), (x 0); simpl in *;
      split; intros; try congruence; try tauto.
Qed.

Theorem cycle_odd_unsat (n : nat) : n mod 2 = 1 -> ~ SatSys (cycle n).
Proof.
  intros Hn [x Hx].
  assert (Hpos : 0 < n) by (destruct n; [simpl in Hn; discriminate|lia]).
  assert (Halt : x (n - 1) = x 0).
  { apply (solution_alternates n x Hx (n - 1)); [lia|]. mod2 n; mod2 (n - 1); lia. }
  assert (Hm : In (n - 1, (S (n - 1)) mod n) (cycle n))
    by (apply mem_cycle; exists (n - 1); split; [lia|auto]).
  pose proof (Hx _ Hm) as Hc.
  simpl in Hc. rewrite succ_mod_of_eq in Hc by lia. exact (Hc Halt).
Qed.

Theorem cycle_sat_iff (n : nat) : SatSys (cycle n) <-> n mod 2 = 0.
Proof.
  split.
  - intros Hs. mod2 n. destruct (Nat.eq_dec (n mod 2) 0) as [Hz|Hz]; auto.
    exfalso; apply (cycle_odd_unsat n); [lia|auto].
  - apply cycle_even_sat.
Qed.

(** ** Every proper piece of the cycle is satisfiable *)

Definition pathAssign (j i : nat) : bool := if Nat.leb i j then par i else par (S i).

Theorem path_sat (n j : nat) :
  j < n -> exists x : nat -> bool, forall i, i < n -> i <> j -> x i <> x ((S i) mod n).
Proof.
  intros Hj. mod2 n. destruct (Nat.eq_dec (n mod 2) 0) as [Hn|Hn].
  - destruct (cycle_even_sat n Hn) as [x Hx]. exists x; intros i Hi _.
    exact (Hx (i, (S i) mod n) (proj2 (mem_cycle n _) (ex_intro _ i (conj Hi eq_refl)))).
  - exists (pathAssign j); intros i Hi Hij.
    destruct (Nat.lt_ge_cases (S i) n) as [Hlt|Hge].
    + rewrite succ_mod_of_lt by auto. unfold pathAssign.
      destruct (Nat.lt_ge_cases i j) as [H1|H1].
      * replace (Nat.leb i j) with true by (symmetry; apply Nat.leb_le; lia).
        replace (Nat.leb (S i) j) with true by (symmetry; apply Nat.leb_le; lia).
        apply par_ne_succ.
      * replace (Nat.leb i j) with false by (symmetry; apply Nat.leb_gt; lia).
        replace (Nat.leb (S i) j) with false by (symmetry; apply Nat.leb_gt; lia).
        apply par_ne_succ.
    + rewrite succ_mod_of_eq by lia. unfold pathAssign.
      replace (Nat.leb i j) with false by (symmetry; apply Nat.leb_gt; lia).
      replace (Nat.leb 0 j) with true by reflexivity.
      assert (H1 : par (S i) = true).
      { destruct (par (S i)) eqn:E; auto. apply par_eq_false_iff in E.
        replace (S i) with n in E by lia. lia. }
      rewrite H1; discriminate.
Qed.

Theorem missing_constraint_sat (n : nat) (S : System) :
  (forall p, In p S -> In p (cycle n)) ->
  (exists j, j < n /\ ~ In (j, (Datatypes.S j) mod n) S) -> SatSys S.
Proof.
  intros HS [j [Hj HjS]].
  destruct (path_sat n j Hj) as [x Hx]. exists x; intros p Hp.
  destruct (proj1 (mem_cycle n p) (HS p Hp)) as [i [Hi Hpi]]; subst p; simpl.
  apply Hx; auto. intros Heq; subst; contradiction.
Qed.

Definition pair_eq_dec (p q : nat * nat) : {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Lemma forall_or_exists (P : nat -> Prop) (Pdec : forall j, {P j} + {~ P j}) (n : nat) :
  (forall j, j < n -> P j) \/ (exists j, j < n /\ ~ P j).
Proof.
  induction n as [|n IH].
  - left; intros j Hj; lia.
  - destruct IH as [IH|[j [Hj Hn]]].
    + destruct (Pdec n) as [Hp|Hp].
      * left; intros j Hj. destruct (Nat.eq_dec j n); [subst; auto|apply IH; lia].
      * right; exists n; split; [lia|auto].
    + right; exists j; split; [lia|auto].
Qed.

Theorem short_subsystem_misses (n : nat) (S : System) :
  length S < n -> exists j, j < n /\ ~ In (j, (Datatypes.S j) mod n) S.
Proof.
  intros Hlen.
  destruct (forall_or_exists (fun j => In (j, (Datatypes.S j) mod n) S)
    (fun j => in_dec pair_eq_dec _ S) n) as [Hall|Hex]; auto.
  exfalso.
  assert (Hsub : incl (seq 0 n) (map fst S)).
  { intros j Hj. apply in_seq in Hj. apply in_map_iff.
    exists (j, (Datatypes.S j) mod n); split; auto; apply Hall; lia. }
  assert (H : length (seq 0 n) <= length (map fst S))
    by (apply NoDup_incl_length; [apply seq_NoDup|exact Hsub]).
  rewrite length_seq, length_map in H. lia.
Qed.

Theorem short_subsystem_sat (n : nat) (S : System) :
  (forall p, In p S -> In p (cycle n)) -> length S < n -> SatSys S.
Proof.
  intros HS Hlen. apply (missing_constraint_sat n S HS (short_subsystem_misses n S Hlen)).
Qed.

(** ** Local consistency *)

Definition LocallyConsistent (k : nat) (sys : System) : Prop :=
  forall S : System, (forall p, In p S -> In p sys) -> length S <= k -> SatSys S.

Lemma locallyConsistent_mono (k k' : nat) (sys : System) :
  k' <= k -> LocallyConsistent k sys -> LocallyConsistent k' sys.
Proof. intros H Hk S HS Hlen; apply Hk; auto; lia. Qed.

Theorem odd_cycle_locally_consistent (n : nat) :
  n mod 2 = 1 -> LocallyConsistent (n - 1) (cycle n) /\ ~ SatSys (cycle n).
Proof.
  intros Hn. assert (Hpos : 0 < n) by (destruct n; [simpl in Hn; discriminate|lia]).
  split; [|apply cycle_odd_unsat; auto].
  intros S HS Hlen; apply (short_subsystem_sat n S HS); lia.
Qed.

Theorem local_consistency_insufficient (k : nat) :
  exists sys : System, LocallyConsistent k sys /\ ~ SatSys sys.
Proof.
  assert (Hodd : (2 * k + 1) mod 2 = 1) by (mod2 (2 * k + 1); lia).
  destruct (odd_cycle_locally_consistent (2 * k + 1) Hodd) as [H1 H2].
  exists (cycle (2 * k + 1)); split; auto.
  apply (locallyConsistent_mono (2 * k + 1 - 1)); auto; lia.
Qed.

Theorem no_local_to_global (k : nat) :
  ~ (forall sys : System, LocallyConsistent k sys -> SatSys sys).
Proof.
  intros Hall. destruct (local_consistency_insufficient k) as [sys [Hloc Hunsat]].
  exact (Hunsat (Hall sys Hloc)).
Qed.

(** ** The same systems as 2-CNF formulas *)

Record Lit := mkLit { var : nat; pos : bool }.
Definition Clause := list Lit.
Definition CNF := list Clause.

Definition evalLit (a : nat -> bool) (l : Lit) : bool := Bool.eqb (a (var l)) (pos l).

Fixpoint evalClause (a : nat -> bool) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' => evalLit a l || evalClause a c'
  end.

Fixpoint evalCNF (a : nat -> bool) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | c :: phi' => evalClause a c && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a, evalCNF a phi = true.

Fixpoint sysCNF (sys : System) : CNF :=
  match sys with
  | [] => []
  | (i, j) :: s => [mkLit i true; mkLit j true] :: [mkLit i false; mkLit j false] :: sysCNF s
  end.

Theorem sysCNF_iff (x : nat -> bool) (sys : System) :
  evalCNF x (sysCNF sys) = true <-> Solves x sys.
Proof.
  induction sys as [|[i j] s IH]; simpl.
  - split; auto. intros _ p [].
  - unfold evalLit; simpl. rewrite !andb_true_iff, IH. split.
    + intros [H1 [H2 H3]] q [Hq|Hq].
      * subst q; simpl. destruct (x i), (x j); simpl in *; discriminate.
      * apply H3; auto.
    + intros H. assert (Hij : x i <> x j) by exact (H (i, j) (or_introl eq_refl)).
      split; [|split].
      * destruct (x i), (x j); simpl; congruence.
      * destruct (x i), (x j); simpl; congruence.
      * intros q Hq; apply H; simpl; auto.
Qed.

Theorem cycleCNF_sat_iff (n : nat) : Satisfiable (sysCNF (cycle n)) <-> n mod 2 = 0.
Proof.
  rewrite <- cycle_sat_iff. split.
  - intros [x Hx]; exists x; apply sysCNF_iff; auto.
  - intros [x Hx]; exists x; apply sysCNF_iff; auto.
Qed.
