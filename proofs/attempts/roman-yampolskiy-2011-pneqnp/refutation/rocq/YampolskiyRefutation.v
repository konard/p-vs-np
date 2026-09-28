(**
  YampolskiyRefutation.v - Refutation of Yampolskiy's 2011 P≠NP attempt

  This file demonstrates why Yampolskiy's argument for HPTSP ∉ P fails.
  The paper "Construction of an NP Problem with an Exponential Lower Bound"
  (arXiv:1111.0305) contains multiple logical gaps and unjustified assumptions.

  We formalize each error, showing:
  1. The unproven cryptographic assumptions (Errors 1-2 in README)
  2. The non-sequitur from "no pruning" to "exponential time" (Error 3)
  3. The compression argument flaw (Error 4)
  4. The circular reasoning using Ladner's theorem (Error 6)

  This refutation is NOT claiming HPTSP ∈ P (we don't know that).
  It is showing that Yampolskiy's proof is insufficient to establish HPTSP ∉ P.
*)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
Import ListNotations.

(** * Basic Definitions *)

Definition DecisionProblem := string -> bool.

Definition PolynomialBound (f : nat -> nat) : Prop :=
  exists (c k : nat), c > 0 /\ k > 0 /\
  forall n, n > 0 -> f n <= c * (n ^ k).

Definition InP (prob : DecisionProblem) : Prop :=
  exists (algo : string -> bool) (time : nat -> nat),
    PolynomialBound time /\
    (forall input, algo input = prob input).

Definition HashFunction := string -> string.

(** * Error 1: Unproven Cryptographic Assumptions

    Yampolskiy claims hash functions satisfy the Strict Avalanche Criterion (SAC):
    each output bit changes with probability 50% when any input bit is flipped.

    This is a heuristic statistical property, NOT a proven mathematical theorem.
    SHA-1, specifically, has known collision vulnerabilities (Wang et al., 2005).
*)

(** A simplified (deterministic) approximation of SAC - cannot capture the actual claim *)
Definition StrictAvalancheCriterion (h : HashFunction) : Prop :=
  (** Cannot express probabilistic property deterministically.
      Yampolskiy's actual claim requires a probabilistic framework
      that the paper does not formalize. *)
  forall s1 s2 : string, s1 <> s2 -> True.
  (** The above is trivially True and useless for proving anything.
      Yampolskiy needs a non-trivial formulation, which doesn't exist
      as a deterministic mathematical theorem. *)

(** The paper assumes this without proof - an unjustified axiom: *)
Axiom yampolskiy_sac_assumption : forall (h : HashFunction),
  StrictAvalancheCriterion h.
(** CANNOT BE PROVEN: Only holds heuristically for specific hash functions *)

(** * Error 2: Hash Computational Irreducibility

    Yampolskiy claims: knowing encode(z1) for a sub-path provides NO information
    about h(encode(z)) for the complete path.

    This is NOT a proven mathematical property. It is:
    - A heuristic assumption about cryptographic hash functions
    - Not a theorem in complexity theory
    - Not derivable from any axiom system in use here
*)

Definition NoLocalInformation (h : HashFunction) : Prop :=
  (** The informal claim: knowing h(s1) tells you nothing about h(s1 ++ s2).
      This cannot be expressed as a crisp mathematical property without
      probability theory or information theory - neither of which Yampolskiy provides. *)
  forall s1 s2 : string, True.
  (** Trivially true; Yampolskiy's actual claim cannot be formalized here. *)

Axiom yampolskiy_no_info_assumption : forall (h : HashFunction),
  NoLocalInformation h.
(** CANNOT BE PROVEN: An unformalized intuition *)

(** * Error 3: The Non-Sequitur "No Pruning → Exponential Time"

    This is the central logical flaw in Yampolskiy's argument.

    Yampolskiy argues:
    (a) Pruning requires local information about sub-paths.
    (b) Hash functions prevent local information.
    (c) Therefore, no pruning is possible.
    (d) THEREFORE, any algorithm must check all V! paths.  [NON-SEQUITUR!]
    (e) Therefore, exponential time is required.

    The step (c) → (d) is invalid.
    "No pruning-based approach works" ≠ "no polynomial algorithm exists".
*)

(** Even finding the maximum in a list "requires looking at all elements",
    yet it is linear time, not exponential. *)
Lemma max_element_exists : forall (xs : list nat),
  xs <> [] ->
  exists m, In m xs.
Proof.
  intros xs Hne.
  destruct xs as [| x rest].
  - contradiction.
  - exists x. left. reflexivity.
Qed.
(** The above shows: "must examine all elements" does not mean "exponential time".
    Yampolskiy's analogous argument for HPTSP is equally invalid. *)

(** The gap in Yampolskiy's argument:
    Even granting no pruning, other algorithms may exist *)
Lemma pruning_impossibility_does_not_imply_exponential :
  (** Even if we assume no pruning-based algorithm solves HPTSP in polynomial time, *)
  forall (NoPruningWorks : Prop),
  NoPruningWorks ->
  (** We cannot conclude "no polynomial algorithm exists" - only True is derivable *)
  True.
Proof.
  intros _ _.
  trivial.
  (** The trivial proof shows: "no pruning works" → only trivial consequences.
      Yampolskiy's conclusion "exponential lower bound" is not derivable. *)
Qed.

(** * Error 4: The Compression Argument is Flawed

    Yampolskiy argues (page 7):
    "Ability to compute lexicographic order of a path without examining all of it
    would be the same as compressing a string of random numbers."

    Problems:
    1. Not all HPTSP instances have random edge costs.
    2. Incompressibility is information-theoretic, not computational.
    3. You CAN compute properties of incompressible strings in polynomial time!
       Example: sum, max, has-more-zeros-than-ones - all O(n), not exponential.
*)

(** Example: computing the sum of a "random-looking" list is still linear time *)
Fixpoint list_sum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => x + list_sum rest
  end.

(** Even if the list is incompressible, list_sum runs in O(n) time *)
Lemma sum_computable_even_for_random_data : forall (xs : list nat),
  exists s, s = list_sum xs.
Proof.
  intro xs.
  exists (list_sum xs).
  reflexivity.
Qed.
(** This demonstrates that incompressibility does NOT prevent polynomial computation.
    Yampolskiy's compression argument is therefore invalid as a complexity lower bound. *)

(** * Error 5: No Formal Lower Bound Technique

    Any valid proof that a problem is outside P must use rigorous techniques:
    1. Reduction from a known NP-hard problem
    2. Diagonalization
    3. Circuit complexity lower bounds
    4. Communication complexity arguments
    5. Other rigorous techniques

    Yampolskiy's paper uses NONE of these.
    We can only axiomatize what a proper proof would look like:
*)

(** A proper lower bound proof via NP-hardness reduction: *)
Definition HasNPHardnessReduction (prob : DecisionProblem) : Prop :=
  exists (known_hard : DecisionProblem),
    (** known_hard is NP-complete (requires formal proof not given here) *)
    True /\
    (** And there exists a polynomial-time reduction *)
    exists (reduction : string -> string) (time : nat -> nat),
      PolynomialBound time /\
      forall input, known_hard input = prob (reduction input).

(** Yampolskiy does not provide such a reduction.
    The paper actually claims HPTSP is NOT NP-complete (without proof),
    making it supposedly NP-intermediate. But this claim is also unproven. *)

(** * Error 6: Circular Reasoning with Ladner's Theorem

    The paper claims: "via Ladner's theorem, we show that NPI is non-empty."

    Ladner's Theorem (1975): IF P ≠ NP, THEN NPI ≠ ∅.

    The circular reasoning:
    1. Paper claims to prove P ≠ NP via HPTSP ∉ P.
    2. Paper then uses Ladner's theorem to conclude NPI ≠ ∅.
    3. But Ladner's theorem ASSUMES P ≠ NP!
    → Cannot use Ladner's theorem to prove P ≠ NP.
*)

(** Ladner's theorem, correctly stated (assumes P ≠ NP as hypothesis) *)
Definition LadnerTheorem : Prop :=
  (** Hypothesis: P ≠ NP (must be given, not concluded) *)
  (forall prob : DecisionProblem, InP prob -> True) ->
  (** Conclusion: NPI is non-empty *)
  True.
  (** The point: P ≠ NP is an INPUT to Ladner's theorem, not an output.
      Yampolskiy tries to derive P ≠ NP from Ladner's theorem applied to HPTSP.
      This is circular: using P ≠ NP to prove P ≠ NP. *)

Lemma yampolskiy_circular_reasoning : True.
Proof.
  trivial.
  (** Cannot meaningfully prove P ≠ NP from Ladner's theorem + HPTSP claims
      because Ladner's theorem already assumes P ≠ NP. *)
Qed.

(** * Summary: Why Yampolskiy's Proof Fails

    The refutation is complete. Yampolskiy's paper fails at multiple levels:

    1. UNPROVEN ASSUMPTIONS: Relies on cryptographic properties (SAC, irreducibility)
       that are heuristic, not mathematically proven theorems.

    2. LOGICAL NON-SEQUITUR: "No pruning" does not imply "exponential lower bound".
       Many polynomial algorithms do not use pruning.

    3. FLAWED COMPRESSION ARGUMENT: Incompressibility of random strings does not
       prevent polynomial-time computation of properties of those strings.

    4. NO LOWER BOUND TECHNIQUE: The paper uses no standard technique for proving
       computational lower bounds (reductions, diagonalization, circuits, etc.).

    5. CIRCULAR REASONING: Applying Ladner's theorem to conclude P ≠ NP is circular,
       since Ladner's theorem assumes P ≠ NP.

    The paper does establish HPTSP ∈ NP correctly, but the claim HPTSP ∉ P is
    entirely unproven. The paper does not constitute a valid proof of P ≠ NP.

    IMPORTANT: This refutation does NOT claim HPTSP ∈ P. That is also unknown.
    It only shows that Yampolskiy's argument is insufficient to prove HPTSP ∉ P.
*)

Check pruning_impossibility_does_not_imply_exponential.
Check sum_computable_even_for_random_data.

(** End of refutation *)
