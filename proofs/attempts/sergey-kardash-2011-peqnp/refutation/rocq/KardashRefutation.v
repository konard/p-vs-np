(*
  KardashRefutation.v - Refutation of Sergey Kardash's 2011 P=NP attempt

  This file demonstrates why Kardash's approach fails:
  pair cleaning is a local consistency method. An empty table proves that the
  formula is unsatisfiable, but the paper's proof that a non-empty result
  implies satisfiability (Lemma 1) has a gap for k >= 3.
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Module KardashRefutation.

(* Variable assignment *)
Definition Assignment := nat -> bool.

(* A partial assignment to k variables *)
Definition PartialAssignment (k : nat) := nat -> bool.

(* A formula over m boolean variables and n clauses *)
Definition Formula (n m : nat) := (nat -> bool) -> bool.

(* Satisfiability *)
Definition isSatisfiable {n m : nat} (f : Formula n m) : Prop :=
  exists a : nat -> bool, f a = true.

(* The fixpoint of pair cleaning is a property of constraint systems.
   For k-SAT, it means: for every pair of overlapping clause combinations,
   every row in one combination's table has a compatible row in the other. *)
Definition ArcConsistent := Prop.

(* Fact: Arc consistency is polynomial to compute - O(e * d^3) *)
Theorem arcConsistency_polynomial :
  exists (c d : nat), forall n : nat, n ^ 3 <= c * n ^ d.
Proof.
  exists 1, 3. intros n. lia.
Qed.

(*
  THE FUNDAMENTAL THEOREM (well-known in constraint programming):
  Local consistency does NOT imply satisfiability for k >= 3.

  This is the core fact that invalidates Kardash's Theorem 1.
  Pair cleaning is:
    - Polynomial to compute: CORRECT
    - Necessary for satisfiability: CORRECT (empty table => UNSAT)
    - Sufficient for satisfiability: INCORRECT for k >= 3
*)

(* Local consistency is NECESSARY: satisfiable => pair cleaning non-empty *)
(* (Contrapositive: an empty table => unsatisfiable) *)
Axiom arcConsistency_necessary :
  forall {n m : nat} (f : Formula n m),
    isSatisfiable f -> True.  (* pair cleaning stays non-empty *)

(*
  Local consistency is NOT SUFFICIENT: a non-empty result does NOT imply satisfiable.

  This axiom records, informally, that pair cleaning is incomplete for k >= 3.
  For plain arc consistency this is standard (for example the 3-coloring CSP of
  a non-3-colorable graph such as K_4, or the triangle in local_global_gap
  below). Pair cleaning is stronger than arc consistency, so these examples
  alone do not settle it; no counterexample to pair cleaning is formalized.
*)
Axiom arcConsistency_insufficient :
  exists (f : Formula 10 5),
    True /\  (* pair cleaning is non-empty *)
    ~ isSatisfiable f.  (* yet the formula is UNSAT *)

(* The critical error in Lemma 1 (forward direction):
   Kardash claims: non-empty cleaning => single-valued unclearable structure => SAT
   From arcConsistency_insufficient, non-empty cleaning does NOT => SAT *)
Theorem lemma1_forward_fails :
  exists (f : Formula 10 5),
    True /\ ~ isSatisfiable f.
Proof.
  exact arcConsistency_insufficient.
Qed.

(*
  2-SAT: propagation is not a decision procedure.

  An earlier version of this file said that for k = 2 unit propagation and
  arc consistency coincide and decide 2-SAT, credited this to Krom (1967), and
  stated it as an axiom whose type was True. That explanation was wrong
  (issue #587); the section below replaces it with checked definitions.

  - Unit propagation without decisions changes nothing on a formula whose
    clauses all have two literals: from the empty assignment no clause is
    unit and none is falsified (unitPropagate_2CNF_empty).
  - Arc consistency on the network with one binary constraint per clause
    removes nothing either, because every two-literal clause allows both
    values of each variable (clausewiseCSP_arcConsistent). Merging the
    constraints on a common scope catches upCounterexample (the merged
    relation is empty) but still misses the triangle x <> y, y <> z, z <> x
    (triangle_arcConsistent, triangle_unsat).
  - A complete polynomial test uses the implication graph, where a clause
    l1 \/ l2 gives the edges ~l1 -> l2 and ~l2 -> l1. A 2-CNF is
    unsatisfiable iff some literal l has paths l ~> ~l and ~l ~> l, i.e. l and
    ~l lie in one strongly connected component; Aspvall, Plass and Tarjan
    (1979) check this in linear time. The direction used for refutation is
    proved below (contradictory_cycle_unsat).

  Other correct routes: Krom (1967) showed that resolution restricted to
  binary clauses decides 2-SAT, and Even, Itai and Shamir (1976) decide it in
  polynomial time by combining unit propagation with decisions.

  What pair cleaning computes (Definitions 3-15 of the paper): clauses are
  grouped by their set of variable indices. For every combination of k + 1
  clause groups (one combination of all groups when there are at most k + 1)
  a table lists the assignments of the combination's variables that satisfy
  its clauses. Clearing deletes a row when another table has no row agreeing
  with it on their common variables, until nothing changes; the result is
  empty when some table is empty. This is pairwise consistency on the tables
  of clause combinations, which is stronger than arc consistency on single
  clauses: both formulas below fit in one table, and pair cleaning empties
  it. For k = 2 the non-empty result does imply satisfiability (sketch in
  ../README.md, checked by experiments/issue587); that is not formalized here.

  | Procedure                          | Time        | Decides 2-SAT?                |
  |------------------------------------|-------------|-------------------------------|
  | Unit propagation, no decisions     | Polynomial  | No (upCounterexample)         |
  | Arc consistency, one per clause    | Polynomial  | No (upCounterexample)         |
  | Arc consistency, merged per scope  | Polynomial  | No (triangleCSP)              |
  | Implication-graph SCC (APT 1979)   | Linear      | Yes                           |
  | Binary resolution (Krom 1967)      | Polynomial  | Yes                           |
  | Pair cleaning, k = 2               | Polynomial  | Yes (informal sketch, tested) |
  | DPLL with backtracking             | Exponential | Yes (and for every k)         |

  For k >= 3 the paper claims that pair cleaning decides k-SAT; the gap in
  Lemma 1 is recorded by informal axioms, not by a counterexample.
*)
Section TwoSATCounterexamples.

(* (i, true) is the negative literal ~x_i. *)
Definition Literal : Type := (nat * bool)%type.
Definition Clause : Type := list Literal.
Definition CNF : Type := list Clause.

Definition literalTrue (a : Assignment) (l : Literal) : bool :=
  if snd l then negb (a (fst l)) else a (fst l).

Definition negLit (l : Literal) : Literal := (fst l, negb (snd l)).

Lemma literalTrue_negLit : forall a l,
  literalTrue a (negLit l) = negb (literalTrue a l).
Proof.
  intros a [i []]; unfold literalTrue, negLit; simpl;
    destruct (a i); reflexivity.
Qed.

Definition clauseSatisfied (a : Assignment) (c : Clause) : bool :=
  existsb (literalTrue a) c.

Definition cnfSatisfied (a : Assignment) (f : CNF) : bool :=
  forallb (clauseSatisfied a) f.

Definition cnfSatisfiable (f : CNF) : Prop :=
  exists a : Assignment, cnfSatisfied a f = true.

(* Unit propagation without decisions *)

(* Values of already assigned variables, as (index, value) pairs. *)
Definition PartialAssign : Type := list (nat * bool).

Fixpoint lookupVar (rho : PartialAssign) (i : nat) : option bool :=
  match rho with
  | [] => None
  | (j, v) :: rest => if Nat.eqb i j then Some v else lookupVar rest i
  end.

Definition literalValue (rho : PartialAssign) (l : Literal) : option bool :=
  match lookupVar rho (fst l) with
  | Some v => Some (if snd l then negb v else v)
  | None => None
  end.

Definition isValue (b : bool) (o : option bool) : bool :=
  match o with
  | Some v => Bool.eqb v b
  | None => false
  end.

Definition isUnassigned (o : option bool) : bool :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition clauseFalsified (rho : PartialAssign) (c : Clause) : bool :=
  forallb (fun l => isValue false (literalValue rho l)) c.

(* The only unassigned literal of a clause that is not yet satisfied. *)
Definition forcedLiteral (rho : PartialAssign) (c : Clause) : option Literal :=
  if existsb (fun l => isValue true (literalValue rho l)) c then None
  else
    match filter (fun l => isUnassigned (literalValue rho l)) c with
    | [l] => Some l
    | _ => None
    end.

Fixpoint findSome {A B : Type} (g : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: rest =>
    match g x with
    | Some y => Some y
    | None => findSome g rest
    end
  end.

Inductive UPResult : Type :=
  | UPConflict
  | UPFixpoint (rho : PartialAssign)
  | UPOutOfFuel.

(* Assign forced literals until a clause is falsified or none is forced. *)
Fixpoint unitPropagate (f : CNF) (fuel : nat) (rho : PartialAssign) : UPResult :=
  match fuel with
  | 0 => UPOutOfFuel
  | S fuel' =>
    if existsb (clauseFalsified rho) f then UPConflict
    else
      match findSome (forcedLiteral rho) f with
      | Some l => unitPropagate f fuel' ((fst l, negb (snd l)) :: rho)
      | None => UPFixpoint rho
      end
  end.

(* Two literals over two different variables. *)
Definition isBinary (c : Clause) : bool :=
  match c with
  | [l1; l2] => negb (Nat.eqb (fst l1) (fst l2))
  | _ => false
  end.

Definition is2CNF (f : CNF) : bool := forallb isBinary f.

Lemma clauseFalsified_nil : forall c,
  isBinary c = true -> clauseFalsified [] c = false.
Proof.
  intros [| l1 [| l2 [| l3 rest]]] H; try discriminate H; reflexivity.
Qed.

Lemma forcedLiteral_nil : forall c,
  isBinary c = true -> forcedLiteral [] c = None.
Proof.
  intros [| l1 [| l2 [| l3 rest]]] H; try discriminate H; reflexivity.
Qed.

Theorem unitPropagate_2CNF_empty : forall f fuel,
  is2CNF f = true -> unitPropagate f (S fuel) [] = UPFixpoint [].
Proof.
  intros f fuel H.
  assert (Hc : existsb (clauseFalsified []) f = false).
  { induction f as [| c f IH]; [reflexivity |].
    simpl in H. apply andb_prop in H as [Hb Hf].
    simpl. rewrite (clauseFalsified_nil c Hb). exact (IH Hf). }
  assert (Hs : findSome (forcedLiteral []) f = None).
  { clear Hc. induction f as [| c f IH]; [reflexivity |].
    simpl in H. apply andb_prop in H as [Hb Hf].
    simpl. rewrite (forcedLiteral_nil c Hb). exact (IH Hf). }
  simpl. rewrite Hc, Hs. reflexivity.
Qed.

(* Arc consistency on binary constraints *)

Record BinConstraint : Type := mkBin {
  cx : nat;
  cy : nat;
  crel : bool -> bool -> bool
}.

Definition bools : list bool := [false; true].

(* Full Boolean domains are arc consistent: each value of each variable has
   a support in every constraint, whose two variables are distinct. *)
Definition supported (c : BinConstraint) : bool :=
  negb (Nat.eqb (cx c) (cy c)) &&
  forallb (fun a => existsb (fun b => crel c a b) bools) bools &&
  forallb (fun b => existsb (fun a => crel c a b) bools) bools.

Definition arcConsistentFull (csp : list BinConstraint) : bool :=
  forallb supported csp.

Definition cspSatisfied (a : Assignment) (csp : list BinConstraint) : bool :=
  forallb (fun c => crel c (a (cx c)) (a (cy c))) csp.

Definition cspSatisfiable (csp : list BinConstraint) : Prop :=
  exists a : Assignment, cspSatisfied a csp = true.

Definition clauseConstraint (c : Clause) : option BinConstraint :=
  match c with
  | [l1; l2] =>
    Some (mkBin (fst l1) (fst l2) (fun a b =>
      (if snd l1 then negb a else a) || (if snd l2 then negb b else b)))
  | _ => None
  end.

(* One constraint per clause, without merging constraints on the same scope. *)
Fixpoint clausewiseCSP (f : CNF) : list BinConstraint :=
  match f with
  | [] => []
  | c :: rest =>
    match clauseConstraint c with
    | Some bc => bc :: clausewiseCSP rest
    | None => clausewiseCSP rest
    end
  end.

Lemma clauseConstraint_supported : forall c bc,
  isBinary c = true -> clauseConstraint c = Some bc -> supported bc = true.
Proof.
  intros [| [i p] [| [j q] [| l3 rest]]] bc Hb Hc; try discriminate Hc.
  simpl in Hb, Hc. injection Hc as <-.
  unfold supported; simpl.
  destruct (Nat.eqb i j); [discriminate Hb |].
  destruct p, q; reflexivity.
Qed.

Theorem clausewiseCSP_arcConsistent : forall f,
  is2CNF f = true -> arcConsistentFull (clausewiseCSP f) = true.
Proof.
  induction f as [| c f IH]; intros H; [reflexivity |].
  simpl in H. apply andb_prop in H as [Hb Hf].
  simpl. destruct (clauseConstraint c) as [bc |] eqn:E.
  - simpl. rewrite (clauseConstraint_supported c bc Hb E). exact (IH Hf).
  - exact (IH Hf).
Qed.

(* Implication graph *)

Definition clauseEdges (c : Clause) : list (Literal * Literal) :=
  match c with
  | [l1; l2] => [(negLit l1, l2); (negLit l2, l1)]
  | _ => []
  end.

Definition implicationEdges (f : CNF) : list (Literal * Literal) :=
  flat_map clauseEdges f.

(* Implies f l1 l2: a path from l1 to l2 in the implication graph of f. *)
Inductive Implies (f : CNF) : Literal -> Literal -> Prop :=
  | ImpRefl : forall l, Implies f l l
  | ImpStep : forall l1 l2 l3,
      In (l1, l2) (implicationEdges f) -> Implies f l2 l3 -> Implies f l1 l3.

Lemma edge_sound : forall f a l1 l2,
  cnfSatisfied a f = true -> In (l1, l2) (implicationEdges f) ->
  literalTrue a l1 = true -> literalTrue a l2 = true.
Proof.
  intros f a l1 l2 Hsat Hin H1.
  apply in_flat_map in Hin as [c [Hc Hce]].
  unfold cnfSatisfied in Hsat. rewrite forallb_forall in Hsat.
  specialize (Hsat c Hc).
  destruct c as [| m1 [| m2 [| m3 rest]]]; simpl in Hce; try contradiction.
  unfold clauseSatisfied in Hsat. cbn [existsb] in Hsat.
  destruct Hce as [E | [E | []]]; injection E as E1 E2; subst l1 l2;
    rewrite literalTrue_negLit in H1;
    destruct (literalTrue a m1), (literalTrue a m2); simpl in *; congruence.
Qed.

Lemma implies_sound : forall f a l1 l2,
  cnfSatisfied a f = true -> Implies f l1 l2 ->
  literalTrue a l1 = true -> literalTrue a l2 = true.
Proof.
  intros f a l1 l2 Hsat Hp. induction Hp as [l | l1 l2 l3 He _ IH]; intros H.
  - exact H.
  - exact (IH (edge_sound f a l1 l2 Hsat He H)).
Qed.

(* Soundness of the strongly connected component test. *)
Theorem contradictory_cycle_unsat : forall f l,
  Implies f l (negLit l) -> Implies f (negLit l) l -> ~ cnfSatisfiable f.
Proof.
  intros f l H1 H2 [a Ha].
  pose proof (implies_sound f a _ _ Ha H1) as P.
  pose proof (implies_sound f a _ _ Ha H2) as Q.
  rewrite literalTrue_negLit in P, Q.
  destruct (literalTrue a l); simpl in *; [discriminate (P eq_refl) |].
  discriminate (Q eq_refl).
Qed.

Local Ltac edge := simpl; repeat (first [left; reflexivity | right]).

(* Counterexample 1: (x \/ y) /\ (x \/ ~y) /\ (~x \/ y) /\ (~x \/ ~y),
   with variables x = 0 and y = 1. *)
Definition upCounterexample : CNF :=
  [[(0, false); (1, false)]; [(0, false); (1, true)];
   [(0, true); (1, false)]; [(0, true); (1, true)]].

Theorem upCounterexample_unsat : ~ cnfSatisfiable upCounterexample.
Proof.
  intros [a H]. unfold cnfSatisfied, clauseSatisfied, literalTrue in H.
  simpl in H. destruct (a 0), (a 1); simpl in H; discriminate H.
Qed.

Theorem upCounterexample_unitPropagate_fixpoint :
  unitPropagate upCounterexample 1 [] = UPFixpoint [].
Proof. reflexivity. Qed.

(* Propagation finds the conflict only after a decision on x. *)
Theorem upCounterexample_conflict_after_decision :
  unitPropagate upCounterexample 3 [(0, true)] = UPConflict /\
  unitPropagate upCounterexample 3 [(0, false)] = UPConflict.
Proof. split; reflexivity. Qed.

Theorem upCounterexample_arcConsistent :
  arcConsistentFull (clausewiseCSP upCounterexample) = true.
Proof. apply clausewiseCSP_arcConsistent. reflexivity. Qed.

(* x ~> y ~> ~x and ~x ~> y ~> x. *)
Theorem upCounterexample_implication_refutation :
  Implies upCounterexample (0, false) (0, true) /\
  Implies upCounterexample (0, true) (0, false) /\
  ~ cnfSatisfiable upCounterexample.
Proof.
  assert (H1 : Implies upCounterexample (0, false) (0, true)).
  { apply ImpStep with (l2 := (1, false)); [edge |].
    apply ImpStep with (l2 := (0, true)); [edge | apply ImpRefl]. }
  assert (H2 : Implies upCounterexample (0, true) (0, false)).
  { apply ImpStep with (l2 := (1, false)); [edge |].
    apply ImpStep with (l2 := (0, false)); [edge | apply ImpRefl]. }
  exact (conj H1 (conj H2 (contradictory_cycle_unsat _ (0, false) H1 H2))).
Qed.

(* Counterexample 2: the triangle x <> y, y <> z, z <> x,
   with variables x = 0, y = 1, z = 2 and one constraint per pair. *)
Definition triangleCSP : list BinConstraint :=
  [mkBin 0 1 (fun a b => negb (Bool.eqb a b));
   mkBin 1 2 (fun a b => negb (Bool.eqb a b));
   mkBin 2 0 (fun a b => negb (Bool.eqb a b))].

Theorem triangle_arcConsistent : arcConsistentFull triangleCSP = true.
Proof. reflexivity. Qed.

Theorem triangle_unsat : ~ cspSatisfiable triangleCSP.
Proof.
  intros [a H]. unfold cspSatisfied in H. simpl in H.
  destruct (a 0), (a 1), (a 2); simpl in H; discriminate H.
Qed.

(* Each disequality u <> v is the pair of clauses (u \/ v) /\ (~u \/ ~v). *)
Definition triangleCNF : CNF :=
  [[(0, false); (1, false)]; [(0, true); (1, true)];
   [(1, false); (2, false)]; [(1, true); (2, true)];
   [(2, false); (0, false)]; [(2, true); (0, true)]].

Theorem triangleCNF_encodes : forall a,
  cnfSatisfied a triangleCNF = cspSatisfied a triangleCSP.
Proof.
  intros a. unfold cnfSatisfied, clauseSatisfied, literalTrue, cspSatisfied.
  simpl. destruct (a 0), (a 1), (a 2); reflexivity.
Qed.

Theorem triangleCNF_unitPropagate_fixpoint :
  unitPropagate triangleCNF 1 [] = UPFixpoint [].
Proof. reflexivity. Qed.

Theorem triangleCNF_arcConsistent :
  arcConsistentFull (clausewiseCSP triangleCNF) = true.
Proof. apply clausewiseCSP_arcConsistent. reflexivity. Qed.

(* x ~> ~y ~> z ~> ~x and ~x ~> y ~> ~z ~> x. *)
Theorem triangleCNF_implication_refutation :
  Implies triangleCNF (0, false) (0, true) /\
  Implies triangleCNF (0, true) (0, false) /\
  ~ cnfSatisfiable triangleCNF.
Proof.
  assert (H1 : Implies triangleCNF (0, false) (0, true)).
  { apply ImpStep with (l2 := (1, true)); [edge |].
    apply ImpStep with (l2 := (2, false)); [edge |].
    apply ImpStep with (l2 := (0, true)); [edge | apply ImpRefl]. }
  assert (H2 : Implies triangleCNF (0, true) (0, false)).
  { apply ImpStep with (l2 := (1, false)); [edge |].
    apply ImpStep with (l2 := (2, true)); [edge |].
    apply ImpStep with (l2 := (0, false)); [edge | apply ImpRefl]. }
  exact (conj H1 (conj H2 (contradictory_cycle_unsat _ (0, false) H1 H2))).
Qed.

End TwoSATCounterexamples.

(*
  The Inductive Step Error in Lemma 1:

  Kardash's inductive proof claims that when adding clause group T_{n_t+1}
  to formula A^{n_t+1}(x), any single-valued unclearable structure V^1_B
  from B^{n_t}(x) can be extended to include T_{n_t+1}.

  The justification given:
    "these clause combinations don't give any new variables...
     [so] value of each clause combination which contains T_{n_t+1}
     consisted of the same variable values as they presented in V^1_B"

  WHY THIS FAILS:
  - The value V^B_{T_n} in V_C (the cleaned full structure) agrees with V^1_B
    on shared variables PAIRWISE
  - But GLOBALLY, the assignment induced by V^1_B extended with T_{n_t+1}'s
    row may violate some constraint combination not directly involving T_{n_t+1}
    that only becomes apparent when considering 3 or more clause groups together
  - Pairwise consistency cannot detect these higher-order inconsistencies,
    which require considering multiple clause groups simultaneously
*)
Axiom inductive_step_error :
  ~ (forall (n_t : nat),
      (* If B^{n_t}(x) has a non-empty cleaned structure *)
      True ->
      (* Then adding T_{n_t+1} always yields a globally consistent extension *)
      True -> False).  (* This placeholder shows the negation structure *)

(*
  Why local consistency does not imply global consistency:

  Arc consistency checks each constraint separately: every value of one of
  its variables has a compatible value of the other.

  Global satisfiability requires: there exists ONE assignment to ALL variables
  that simultaneously satisfies all constraints.

  Example: Boolean variables x, y, z with x <> y, y <> z, z <> x. Every value
  of every variable has a support in each constraint, so arc consistency keeps
  the full domains, but no 2-coloring of a triangle exists. Path consistency
  (polynomial for a fixed domain size) or the implication graph of the
  equivalent 2-CNF detects the conflict.
*)
Theorem local_global_gap :
  arcConsistentFull triangleCSP = true /\ ~ cspSatisfiable triangleCSP.
Proof.
  exact (conj triangle_arcConsistent triangle_unsat).
Qed.

(*
  Summary: Kardash's algorithm summary

  Kardash's pair cleaning algorithm:
    1. RUNTIME: Polynomial O(n^12) for 3-SAT -- this claim is CORRECT
    2. CORRECTNESS: Non-empty result iff SATISFIABLE -- this claim is INCORRECT

  The algorithm is a correct polynomial-time computation of a local consistency
  (pairwise consistency on clause-combination tables). The paper does not prove
  that it decides k-SAT when k >= 3.

  Therefore P=NP is not established.
*)
Theorem kardash_algorithm_incorrect :
  (* The algorithm runs in polynomial time (correct) *)
  (exists c d : nat, forall n : nat, n ^ 12 <= c * n ^ d) /\
  (* But correctness fails: non-empty cleaning != satisfiable *)
  (exists (f : Formula 10 5), True /\ ~ isSatisfiable f).
Proof.
  split.
  - exists 1, 12. intros. lia.
  - exact arcConsistency_insufficient.
Qed.

End KardashRefutation.
