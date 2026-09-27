(** * Issue #532, Idea 01 -- Exact SAT algorithm (brute force as the baseline)

    Rocq counterpart of [lean/Idea01.lean]; theorem names are aligned.

    Proved for every CNF and every [n]:
    - [length_allAssignments], [mem_allAssignments_iff], [nodup_allAssignments]:
      the enumeration lists exactly the 2^n distinct vectors of length n;
    - [brute_force_sound], [brute_force_complete], [bruteForce_correct]:
      the uniform brute-force decider is correct;
    - [bruteForceCost_le], [bruteForceCost_unsat], [hardFamily_cost]:
      at most 2^n formula evaluations, exactly 2^n on every unsatisfiable
      formula, and an unsatisfiable family with exactly n variables for
      every n >= 1;
    - [numVars_le_encodingLength], [bruteForceCost_le_exp_size],
      [decode_encode], [encode_injective]: an explicit lossless binary encoding;
    - [polySAT_agrees_with_bruteForce]: if the open obligation
      [PolySATDecider] (stated over a finite-table Turing machine) holds, the
      machine outputs the brute-force answer on every formula.

    Verdict: brute force is refuted as a polynomial-time algorithm; a uniform
    polynomial-time SAT decider is equivalent to P = NP (Cook-Levin, not
    formalized here) and remains open.  [PolySATDecider] is a definition,
    never postulated. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(** ** CNF syntax and semantics *)

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

Definition VarsBelow (n : nat) (phi : CNF) : Prop :=
  forall c, In c phi -> forall l, In l c -> var l < n.

Lemma evalClause_congr (a b : Assignment) (n : nat) (c : Clause) :
  (forall i, i < n -> a i = b i) -> (forall l, In l c -> var l < n) ->
  evalClause a c = evalClause b c.
Proof.
  intros hab; induction c as [|l c IH]; intros hc; simpl; auto.
  unfold evalLit. rewrite (hab (var l) (hc l (or_introl eq_refl))).
  rewrite IH; auto. intros l' hl'; apply hc; simpl; auto.
Qed.

Lemma evalCNF_congr (a b : Assignment) (n : nat) (phi : CNF) :
  (forall i, i < n -> a i = b i) -> VarsBelow n phi -> evalCNF a phi = evalCNF b phi.
Proof.
  intros hab; induction phi as [|c phi IH]; intros hphi; simpl; auto.
  rewrite (evalClause_congr a b n c hab (hphi c (or_introl eq_refl))).
  rewrite IH; auto. intros c' hc'; apply hphi; simpl; auto.
Qed.

(** ** Enumerating all assignments *)

Fixpoint allAssignments (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allAssignments n') ++ map (cons true) (allAssignments n')
  end.

Fixpoint toAssign (v : list bool) (i : nat) : bool :=
  match v, i with
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v', S i' => toAssign v' i'
  end.

Fixpoint prefixOf (a : Assignment) (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => a 0 :: prefixOf (fun i => a (S i)) n'
  end.

Theorem length_allAssignments (n : nat) : length (allAssignments n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allAssignments_iff (n : nat) (v : list bool) :
  In v (allAssignments n) <-> length v = n.
Proof.
  revert v; induction n as [|n IH]; intros v.
  - destruct v as [|b v]; simpl; split; intros H; auto; try discriminate.
    destruct H as [H|H]; [discriminate|contradiction].
  - destruct v as [|b v]; simpl; rewrite in_app_iff, !in_map_iff; split.
    + intros [[w [Hw _]]|[w [Hw _]]]; discriminate.
    + intros H; discriminate.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; injection Hw; intros; subst;
        f_equal; apply IH; auto.
    + intros H; injection H; intros H'; destruct b.
      * right; exists v; split; auto; apply IH; auto.
      * left; exists v; split; auto; apply IH; auto.
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

Lemma length_prefixOf (a : Assignment) (n : nat) : length (prefixOf a n) = n.
Proof. revert a; induction n; intros a; simpl; auto. Qed.

Lemma toAssign_prefixOf (a : Assignment) (n i : nat) :
  i < n -> toAssign (prefixOf a n) i = a i.
Proof.
  revert a i; induction n as [|n IH]; intros a i H; [lia|].
  destruct i as [|i]; simpl; auto.
  apply (IH (fun j => a (S j))); lia.
Qed.

(** ** The brute-force decider *)

Definition bruteForce (n : nat) (phi : CNF) : bool :=
  existsb (fun v => evalCNF (toAssign v) phi) (allAssignments n).

Theorem brute_force_sound (n : nat) (phi : CNF) :
  bruteForce n phi = true -> Satisfiable phi.
Proof.
  unfold bruteForce; intros H; apply existsb_exists in H.
  destruct H as [v [_ Hv]]; exists (toAssign v); auto.
Qed.

Theorem brute_force_complete (n : nat) (phi : CNF) :
  VarsBelow n phi -> Satisfiable phi -> bruteForce n phi = true.
Proof.
  intros Hphi [a Ha]; unfold bruteForce; apply existsb_exists.
  exists (prefixOf a n); split.
  - apply mem_allAssignments_iff, length_prefixOf.
  - rewrite (evalCNF_congr (toAssign (prefixOf a n)) a n phi); auto.
    intros i Hi; apply toAssign_prefixOf; auto.
Qed.

(** ** Number of variables *)

Fixpoint clauseBound (c : Clause) : nat :=
  match c with
  | [] => 0
  | l :: c' => Nat.max (S (var l)) (clauseBound c')
  end.

Fixpoint numVars (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => Nat.max (clauseBound c) (numVars phi')
  end.

Lemma clauseBound_cons (l : Lit) (c : Clause) :
  clauseBound (l :: c) = Nat.max (S (var l)) (clauseBound c).
Proof. reflexivity. Qed.

Lemma numVars_cons (c : Clause) (phi : CNF) :
  numVars (c :: phi) = Nat.max (clauseBound c) (numVars phi).
Proof. reflexivity. Qed.

Lemma lt_clauseBound (c : Clause) : forall l, In l c -> var l < clauseBound c.
Proof.
  induction c as [|l c IH]; intros l' Hl'; [contradiction|].
  change (clauseBound (l :: c)) with (Nat.max (S (var l)) (clauseBound c)).
  destruct Hl' as [H|H]; [subst; lia|]. specialize (IH l' H); lia.
Qed.

Lemma varsBelow_numVars (phi : CNF) : VarsBelow (numVars phi) phi.
Proof.
  induction phi as [|c phi IH]; intros c' Hc' l Hl; [contradiction|].
  change (numVars (c :: phi)) with (Nat.max (clauseBound c) (numVars phi)).
  destruct Hc' as [H|H].
  - subst; pose proof (lt_clauseBound c' l Hl); lia.
  - pose proof (IH c' H l Hl); lia.
Qed.

Theorem bruteForce_correct (phi : CNF) :
  bruteForce (numVars phi) phi = true <-> Satisfiable phi.
Proof.
  split; [apply brute_force_sound|apply brute_force_complete, varsBelow_numVars].
Qed.

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

(** ** A lossless binary encoding of CNFs (same token scheme as the Lean file) *)

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

Lemma decodeAux_ticks (v : nat) (r : list bool) (k : nat) (cur : Clause) :
  decodeAux (ticks v ++ r) k cur = decodeAux r (k + v) cur.
Proof.
  revert k; induction v as [|v IH]; intros k; simpl.
  - rewrite Nat.add_0_r; auto.
  - rewrite IH; f_equal; lia.
Qed.

Lemma decodeAux_clause (c : Clause) (r : list bool) (cur : Clause) :
  decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 [].
Proof.
  revert cur; induction c as [|[v p] c IH]; intros cur; simpl.
  - rewrite app_nil_r; auto.
  - unfold encodeLit; simpl. rewrite <- !app_assoc, decodeAux_ticks. simpl.
    rewrite IH, <- app_assoc; auto.
Qed.

Theorem decode_encode (phi : CNF) : decode (encodeCNF phi) = phi.
Proof.
  unfold decode; induction phi as [|c phi IH]; simpl; auto.
  rewrite decodeAux_clause, IH; auto.
Qed.

Theorem encode_injective (phi psi : CNF) : encodeCNF phi = encodeCNF psi -> phi = psi.
Proof.
  intros H; rewrite <- (decode_encode phi), H; apply decode_encode.
Qed.

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

(** ** The open obligation over an explicit finite-table machine *)

Inductive Symbol := blank | zero | one.

Definition symOfBool (b : bool) : Symbol := if b then one else zero.

Definition symIndex (s : Symbol) : nat :=
  match s with blank => 0 | zero => 1 | one => 2 end.

Inductive Direction := DLeft | DRight | DStay.

Inductive Instruction :=
| Halt (answer : bool)
| Move (nextState : nat) (write : Symbol) (d : Direction).

Record Machine := mkMachine { program : list (list Instruction) }.

Record Config := mkConfig { state : nat; ltape : list Symbol; head : Symbol; rtape : list Symbol }.

Definition initial (input : list bool) : Config :=
  match map symOfBool input with
  | [] => mkConfig 0 [] blank []
  | a :: rest => mkConfig 0 [] a rest
  end.

Definition instruction (m : Machine) (q : nat) (a : Symbol) : Instruction :=
  match nth_error (program m) q with
  | Some row => match nth_error row (symIndex a) with Some i => i | None => Halt false end
  | None => Halt false
  end.

Definition moveHead (c : Config) (next : nat) (w : Symbol) (d : Direction) : Config :=
  match d with
  | DStay => mkConfig next (ltape c) w (rtape c)
  | DLeft => match ltape c with
             | [] => mkConfig next [] blank (w :: rtape c)
             | a :: rest => mkConfig next rest a (w :: rtape c)
             end
  | DRight => match rtape c with
              | [] => mkConfig next (w :: ltape c) blank []
              | a :: rest => mkConfig next (w :: ltape c) a rest
              end
  end.

Definition step (m : Machine) (c : Config) : bool + Config :=
  match instruction m (state c) (head c) with
  | Halt b => inl b
  | Move next w d => inr (moveHead c next w d)
  end.

Inductive Run (m : Machine) : Config -> nat -> bool -> Prop :=
| RHalt c b : step m c = inl b -> Run m c 1 b
| RNext c c' t b : step m c = inr c' -> Run m c' t b -> Run m c (S t) b.

Record Polynomial := mkPoly { coefficient : nat; degree : nat }.

Definition evalPoly (p : Polynomial) (n : nat) : nat := coefficient p * (n + 1) ^ degree p.

(** Open obligation (equivalent to P = NP by Cook-Levin, not formalized). *)
Definition PolySATDecider : Prop :=
  exists (M : Machine) (p : Polynomial), forall phi : CNF, exists t b,
    t <= evalPoly p (length (encodeCNF phi)) /\ Run M (initial (encodeCNF phi)) t b /\
    (b = true <-> Satisfiable phi).

Theorem polySAT_agrees_with_bruteForce :
  PolySATDecider ->
  exists (M : Machine) (p : Polynomial), forall phi : CNF, exists t,
    t <= evalPoly p (length (encodeCNF phi)) /\
    Run M (initial (encodeCNF phi)) t (bruteForce (numVars phi) phi).
Proof.
  intros [M [p HM]]; exists M, p; intros phi.
  destruct (HM phi) as [t [b [Ht [Hr Hb]]]]; exists t; split; auto.
  replace (bruteForce (numVars phi) phi) with b; auto.
  pose proof (bruteForce_correct phi) as Hbf.
  destruct b, (bruteForce (numVars phi) phi) eqn:E; auto.
  - exfalso. assert (Hs : Satisfiable phi) by (apply Hb; auto).
    apply Hbf in Hs; congruence.
  - exfalso. assert (Hs : Satisfiable phi) by (apply Hbf; auto).
    apply Hb in Hs; discriminate.
Qed.
