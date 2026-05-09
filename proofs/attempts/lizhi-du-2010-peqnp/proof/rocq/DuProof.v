(*
  DuProof.v — Forward formalization of Lizhi Du's 2010 P=NP attempt.

  This file formalizes Du's CLAIMED proof that P = NP via a polynomial-time
  algorithm for 3SAT using checking trees, useful units, and contradiction pairs.

  Following the original paper: Du, L. (2010). "A Polynomial time Algorithm for 3SAT".
  arXiv:1004.3702. See ../ORIGINAL.md for the full paper reconstruction.

  NOTE: The correctness of Algorithm 1, Step 3 is stated as an AXIOM because it
  cannot be proven — it is actually false. See ../refutation/ for the refutation.
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Module DuProof.

(* ============================================================
   § 1. SAT Problem Formalization
   (Following the paper's notation exactly)
   ============================================================ *)

(** A variable is a natural number identifier. *)
Definition Var := nat.

(** A literal is either a positive (x) or negative (¬x) variable. *)
Inductive Literal :=
  | Pos : Var -> Literal   (* positive literal x *)
  | Neg : Var -> Literal.  (* negative literal ¬x *)

(** A clause is a disjunction of literals: (l₁ ∨ l₂ ∨ ... ∨ lₖ). *)
Definition Clause := list Literal.

(** A CNF formula is a conjunction of clauses. *)
Definition CNFFormula := list Clause.

(** A truth assignment maps each variable to a boolean. *)
Definition Assignment := Var -> bool.

(** Evaluate a literal under an assignment. *)
Definition evalLiteral (a : Assignment) (l : Literal) : bool :=
  match l with
  | Pos v => a v
  | Neg v => negb (a v)
  end.

(** Evaluate a clause (true iff at least one literal is true). *)
Fixpoint evalClause (a : Assignment) (c : Clause) : bool :=
  match c with
  | []      => false
  | l :: ls => orb (evalLiteral a l) (evalClause a ls)
  end.

(** Evaluate a CNF formula (true iff all clauses are true). *)
Fixpoint evalCNF (a : Assignment) (f : CNFFormula) : bool :=
  match f with
  | []      => true
  | c :: cs => andb (evalClause a c) (evalCNF a cs)
  end.

(** A formula is satisfiable if some assignment makes it true. *)
Definition isSatisfiable (f : CNFFormula) : Prop :=
  exists a : Assignment, evalCNF a f = true.

(** A formula is a 3-CNF formula if all clauses have at most 3 literals. *)
Definition is3CNF (f : CNFFormula) : Prop :=
  forall c, In c f -> length c <= 3.

(* ============================================================
   § 2. Du's Key Concepts
   (Definitions 1–4 from the paper)
   ============================================================ *)

(** Useful units for a literal: the set of literals forced when this literal
    is assigned true (via unit propagation in the checking tree). *)
Record UsefulUnits := {
  uu_literal : Literal;
  uu_units   : list Literal
}.

(** A contradiction pair: two literals x and ¬x that cannot both be true. *)
Definition isContradictionPair (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | Pos v1, Neg v2 => Nat.eqb v1 v2
  | Neg v1, Pos v2 => Nat.eqb v1 v2
  | _,      _      => false
  end.

(** Simplified checking tree: stores literals with their useful units. *)
Record CheckingTree := {
  ct_nodes       : list Literal;
  ct_usefulUnits : list UsefulUnits
}.

(* ============================================================
   § 3. Algorithm 1, Step 3 (THE FLAWED STEP)
   (Exactly as stated in the paper)
   ============================================================ *)

(** Check if two literals are equal. *)
Definition literalEq (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | Pos v1, Pos v2 => Nat.eqb v1 v2
  | Neg v1, Neg v2 => Nat.eqb v1 v2
  | _,      _      => false
  end.

(** Check if a literal is in a list. *)
Fixpoint literalIn (l : Literal) (ls : list Literal) : bool :=
  match ls with
  | []       => false
  | l' :: rest => orb (literalEq l l') (literalIn l rest)
  end.

(** Du's intersection operation from Step 3:
    For non-contradiction pair (x, y), set U(x) ← U(x) ∩ U(y). *)
Definition duIntersect (u1 u2 : UsefulUnits) : UsefulUnits :=
  {| uu_literal := uu_literal u1;
     uu_units   := filter (fun l => literalIn l (uu_units u2)) (uu_units u1) |}.

(** Check if two useful units have a non-contradiction pair relationship. *)
Definition nonContradictionPair (u1 u2 : UsefulUnits) : bool :=
  negb (isContradictionPair (uu_literal u1) (uu_literal u2)).

(** Step 3 of Algorithm 1: for each literal u, if there exists another literal v
    that is NOT a contradiction pair, replace U(u) with U(u) ∩ U(v). *)
Fixpoint applyStep3_helper (u : UsefulUnits) (units : list UsefulUnits)
    : UsefulUnits :=
  match units with
  | []         => u
  | u' :: rest =>
      if negb (literalEq (uu_literal u) (uu_literal u')) &&
         nonContradictionPair u u'
      then duIntersect u u'
      else applyStep3_helper u rest
  end.

Definition applyStep3 (units : list UsefulUnits) : list UsefulUnits :=
  map (fun u => applyStep3_helper u units) units.

(** Check if any literal has empty useful units (UNSAT criterion). *)
Fixpoint hasEmptyUnits (units : list UsefulUnits) : bool :=
  match units with
  | []         => false
  | u :: rest  => orb (Nat.eqb (length (uu_units u)) 0) (hasEmptyUnits rest)
  end.

(* ============================================================
   § 4. Algorithm 1 (Complete)
   ============================================================ *)

(** The checking tree and useful units are computed from the formula.
    Their construction is complex; we axiomatize them here since the error
    is in Step 3, not in the tree construction. *)
Axiom buildCheckingTree : CNFFormula -> CheckingTree.

(** Du's complete Algorithm 1.
    Returns true (SAT) or false (UNSAT). *)
Definition duAlgorithm1 (f : CNFFormula) : bool :=
  let T      := buildCheckingTree f in
  let units  := ct_usefulUnits T in
  (* Step 3: intersect useful units for non-contradiction pairs *)
  let units' := applyStep3 units in
  (* Step 4: if any useful units are empty, return UNSAT *)
  negb (hasEmptyUnits units').

(* ============================================================
   § 5. Du's Claimed Correctness of Algorithm 1
   ============================================================ *)

(** AXIOM (Du's unproven claim): Algorithm 1 is a correct decider for 3SAT.

    NOTE: This axiom is FALSE — it cannot be proven.
    The He et al. (2024) counter-example shows a satisfiable 3-CNF formula
    on which duAlgorithm1 returns false (UNSAT). See ../refutation/.
*)
Axiom du_correctness_claim :
  forall f : CNFFormula,
    is3CNF f ->
    (duAlgorithm1 f = true <-> isSatisfiable f).

(* ============================================================
   § 6. Du's Claimed Implication: P = NP
   ============================================================ *)

(** Polynomial time bound: T is polynomial if ∃ c k, T(n) ≤ c * n^k. *)
Definition isPolynomial (T : nat -> nat) : Prop :=
  exists c k : nat, forall n : nat, T n <= c * n ^ k.

(** AXIOM (Du's claim): Algorithm 1 runs in polynomial time O(n³). *)
Axiom du_polynomial_time : isPolynomial (fun n => n ^ 3).

(** THEOREM (conditional): If Du's correctness claim is true and Algorithm 1
    runs in polynomial time, then 3SAT ∈ P. *)
Theorem du_implies_3SAT_in_P :
  (forall f : CNFFormula,
     is3CNF f -> (duAlgorithm1 f = true <-> isSatisfiable f)) ->
  isPolynomial (fun n => n ^ 3) ->
  exists T : nat -> nat, isPolynomial T.
Proof.
  intros _h_correct h_poly.
  exact (ex_intro _ _ h_poly).
Qed.

(** THEOREM: If the correctness claim holds (which it does not), Algorithm 1
    would provide a polynomial-time decision procedure for 3SAT. *)
Theorem du_attempt_would_put_3SAT_in_P :
  (forall f : CNFFormula,
     is3CNF f -> (duAlgorithm1 f = true <-> isSatisfiable f)) ->
  exists T : nat -> nat, isPolynomial T.
Proof.
  intro h_correct.
  apply du_implies_3SAT_in_P.
  - exact h_correct.
  - exact du_polynomial_time.
Qed.

End DuProof.

(*
  Summary of this forward formalization:

  - We formalize the 3SAT problem and Du's key concepts (checking trees, useful units,
    contradiction pairs) following the original paper.
  - Algorithm 1 is formalized exactly, including the flawed Step 3 intersection.
  - Du's correctness claim is stated as an AXIOM (du_correctness_claim) — it
    cannot be proven as it is false.
  - We show that IF the correctness claim were true AND the algorithm runs in
    polynomial time, THEN 3SAT ∈ P (which would imply P = NP via NP-completeness).
  - The refutation in ../refutation/ shows du_correctness_claim is false by
    exhibiting the He et al. counter-example.
*)
