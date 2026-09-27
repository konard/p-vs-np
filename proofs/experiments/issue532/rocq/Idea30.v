(* Issue #532, Idea 30: unrestricted circuit lower bounds (transfer and counting).

   Rocq counterpart of lean/Idea30.lean; theorem names are aligned.

   Verdict: developed to an open obligation (conditional theorem proved).

   Everything is stated over the shared layer: the machine model of
   Complexity.v / Machines.v (InP, InNP, SAT) and the shared NAND circuit
   model of Circuits.v (Circuit, wires, output, WF, InPPoly,
   SuperpolyLowerBound).

   - Transfer (lower_bound_transfer, no_fast_algorithm): a circuit lower
     bound, a simulation of fast algorithms by small circuits and a size
     bound together exclude a fast algorithm.  For the machine model the
     simulation is the known theorem PSubsetPPoly (P in P/poly), used only
     as a named hypothesis.
   - Shannon counting: the counting core (words, allBool, fnOfTable,
     uncovered_table, shannon_codes, shannon_circuits) lives in Circuits.v
     over the shared circuit model; this file keeps the concrete instance
     four_bit_function_needs_three_gates.  exists_not_inPPoly (Circuits.v)
     uses counting to show that a language outside P/poly exists.

   Counting is non-explicit: its hard language is not known to be in NP.
   The open obligations are SATCircuitLowerBound (SAT needs superpolynomial
   circuits) and ExplicitNPLowerBound (some NP language does).  With
   PSubsetPPoly (and SATInNP for the SAT version) each gives PNotEqualsNP
   (sat_lower_bound_separates, explicit_lower_bound_separates).  Nothing
   here proves such a bound.

   Difference from Lean: Lean derives superpoly_excludes_poly_circuits and
   const_no_lower_bound from the classical superpoly_iff_not_inPPoly; here
   they use its constructive direction not_inPPoly_of_superpoly, so the
   statements are the same and no excluded middle is needed. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.

(** The abstract conditional contradiction. *)
Theorem lower_bound_transfer (Algorithm Circuit : Type) (compile : Algorithm -> Circuit)
  (fast : Algorithm -> Prop) (correct expensive : Circuit -> Prop) :
  (forall c, correct c -> expensive c) ->
  (forall a, fast a -> correct (compile a)) ->
  (forall a, fast a -> ~ expensive (compile a)) ->
  forall a, ~ fast a.
Proof.
  intros Hlower Hsimulation Hsize a Hfast.
  apply (Hsize a Hfast). apply Hlower, Hsimulation, Hfast.
Qed.

(** * Shannon counting: a concrete instance

    The general counting theorems (words_length, mem_words, words_nodup,
    allBool_length, tables_length, table_of_fnOfTable, cover_length,
    uncovered_table, codesUpTo_length, shannon_codes, shannon_circuits) are
    in Circuits.v, stated over the shared wires / output / WF. *)

(** Concrete instance: some Boolean function on 4 bits needs more than 2
    NAND gates. *)
Theorem four_bit_function_needs_three_gates :
  exists f : Language, forall C, WF 4 C -> length C <= 2 ->
    exists x, length x = 4 /\ output x C <> f x.
Proof. apply shannon_circuits. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

(** * Transfer over the shared model *)

(** A superpolynomial lower bound excludes polynomial-size circuits. *)
Theorem superpoly_excludes_poly_circuits : forall f : Language,
  SuperpolyLowerBound f -> ~ InPPoly f.
Proof. exact not_inPPoly_of_superpoly. Qed.

(** Transfer to algorithms, given the simulation of fast algorithms by
    polynomial-size circuits as a hypothesis (a schema over an abstract
    algorithm type). *)
Theorem no_fast_algorithm {Algorithm : Type} (computes : Algorithm -> Language)
  (fast : Algorithm -> Prop)
  (simulation : forall a, fast a -> InPPoly (computes a))
  (f : Language) :
  SuperpolyLowerBound f -> forall a, fast a -> computes a <> f.
Proof.
  intros h a ha e. apply (superpoly_excludes_poly_circuits f h).
  rewrite <- e. apply simulation. exact ha.
Qed.

(** For the machine model: under [PSubsetPPoly], a language with a
    superpolynomial circuit lower bound is not in P. *)
Theorem not_inP_of_superpoly : PSubsetPPoly -> forall f : Language,
  SuperpolyLowerBound f -> ~ InP f.
Proof.
  intros hP f h. exact (not_inP_of_not_inPPoly hP f (superpoly_excludes_poly_circuits f h)).
Qed.

(** * The open obligations *)

(** Open obligation.  SAT ([SAT] of Machines.v) has a superpolynomial lower
    bound for the shared NAND circuit model.  Not known; classically
    equivalent to [~ InPPoly SAT] ([superpoly_iff_not_inPPoly]). *)
Definition SATCircuitLowerBound : Prop := SuperpolyLowerBound SAT.

(** Open obligation.  Some language in NP (the shared [InNP]) has a
    superpolynomial circuit lower bound, i.e. NP is not in P/poly. *)
Definition ExplicitNPLowerBound : Prop :=
  exists L : Language, InNP L /\ SuperpolyLowerBound L.

(** Schema (the pre-refactor form): an explicit function in a class
    [NPClass] with a superpolynomial circuit lower bound.  It is only as
    strong as the class supplied; [ExplicitNPLowerBound] is its instance at
    [InNP]. *)
Definition ExplicitNPLowerBoundFor (NPClass : Language -> Prop) : Prop :=
  exists f, NPClass f /\ SuperpolyLowerBound f.

Theorem explicitNPLowerBound_iff_for :
  ExplicitNPLowerBound <-> ExplicitNPLowerBoundFor InNP.
Proof. reflexivity. Qed.

(** The SAT obligation implies the NP obligation (given [SATInNP]). *)
Theorem explicit_of_sat : SATInNP -> SATCircuitLowerBound -> ExplicitNPLowerBound.
Proof. intros mem h. exists SAT. split; [exact mem | exact h]. Qed.

(** Conditional theorem (SAT form).  Given the membership half of
    Cook-Levin and the known theorem P in P/poly as named hypotheses, a
    superpolynomial circuit lower bound for SAT gives P <> NP. *)
Theorem sat_lower_bound_separates :
  SATInNP -> PSubsetPPoly -> SATCircuitLowerBound -> PNotEqualsNP.
Proof. exact pNotEqualsNP_of_superpoly_sat. Qed.

(** Conditional theorem.  Given P in P/poly as a named hypothesis, an NP
    language with a superpolynomial circuit lower bound gives P <> NP. *)
Theorem explicit_lower_bound_separates :
  PSubsetPPoly -> ExplicitNPLowerBound -> PNotEqualsNP.
Proof.
  intros hP [L [hL hlb]]. exact (pNotEqualsNP_of_superpoly hP L hL hlb).
Qed.

(** The weaker reading, without [PSubsetPPoly]: the obligation exhibits an
    NP language outside P/poly. *)
Theorem explicit_lower_bound_not_inPPoly :
  ExplicitNPLowerBound -> exists L, InNP L /\ ~ InPPoly L.
Proof.
  intros [L [hL hlb]]. exists L. split; [exact hL |].
  exact (superpoly_excludes_poly_circuits L hlb).
Qed.

(** Schema version of the pre-refactor conditional: the obligation for a
    class [NPClass] plus a simulation hypothesis yields a function in
    [NPClass] computed by no fast algorithm. *)
Theorem explicit_lower_bound_separatesFor {Algorithm : Type}
  (NPClass : Language -> Prop) (computes : Algorithm -> Language)
  (fast : Algorithm -> Prop)
  (simulation : forall a, fast a -> InPPoly (computes a)) :
  ExplicitNPLowerBoundFor NPClass ->
  exists f, NPClass f /\ forall a, fast a -> computes a <> f.
Proof.
  intros [f [hf hlb]]. exists f. split; [exact hf |].
  exact (no_fast_algorithm computes fast simulation f hlb).
Qed.

(** * Non-vacuity *)

(** The constant-false language is decided in one step by the empty machine. *)
Theorem inP_const_false : InP (fun _ => false).
Proof.
  apply (inP_of_decidesWithin {| program := [] |} {| coefficient := 1; degree := 0 |}).
  intro x. exists 1, false. split; [unfold evalPoly; simpl; lia |].
  split; [apply run_halt; destruct x; reflexivity | reflexivity].
Qed.

(** The NP half of [ExplicitNPLowerBound] is satisfiable. *)
Theorem inNP_const_false : InNP (fun _ => false).
Proof. exact (pSubsetNP _ inP_const_false). Qed.

(** The lower-bound half is satisfiable: counting gives a (non-explicit)
    language with a superpolynomial circuit lower bound. *)
Theorem lower_bound_half_satisfiable : exists L : Language, SuperpolyLowerBound L.
Proof. exact exists_superpolyLowerBound. Qed.

(** The lower-bound half is not trivially true: constant languages have
    two- and three-gate circuits, so they have no superpolynomial lower
    bound. *)
Theorem const_no_lower_bound : forall b : bool, ~ SuperpolyLowerBound (fun _ => b).
Proof. intros b h. exact (not_inPPoly_of_superpoly _ h (inPPoly_const b)). Qed.

(** Counting alone proves the schema for the trivial class: the gap to the
    obligation is exactly NP membership of a hard function (explicitness). *)
Theorem counting_gives_schema_for_all_languages :
  ExplicitNPLowerBoundFor (fun _ => True).
Proof.
  destruct exists_superpolyLowerBound as [L hL]. exists L. split; [exact I | exact hL].
Qed.
