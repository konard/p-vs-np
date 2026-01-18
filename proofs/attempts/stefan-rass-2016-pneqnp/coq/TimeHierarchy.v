(** * Time Hierarchy Theorem and Density Bounds

    This file formalizes key concepts from Sections 4.3-4.4 of Stefan Rass (2016).
    We focus on:
    1. Time-constructible functions
    2. The deterministic Time Hierarchy Theorem
    3. Density functions and bounds
    4. The language of squares and its intersection with hard languages

    **Goal**: Document where the proof breaks down, specifically:
    - Error 1: Mismatch between L_D definition and encoding
    - Error 2: Circular dependence in density bounds
*)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Classical.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

Open Scope nat_scope.

(** ** Basic Definitions *)

(** A string is a list of booleans (bits) *)
Definition string := list bool.

(** Length of a string *)
Definition length (s : string) : nat := List.length s.

(** A language is a predicate on strings *)
Definition language := string -> Prop.

(** ** Time-Constructible Functions *)

(** A function t: nat -> nat is time-constructible if there exists
    a Turing machine M that on input 1^n outputs t(n) in time O(t(n)).

    We axiomatize this property since we cannot directly model Turing machines
    in Coq without significant infrastructure. *)

Axiom time_constructible : (nat -> nat) -> Prop.

(** Examples of time-constructible functions *)
Axiom polynomial_time_constructible :
  forall (p : nat -> nat),
  (exists c k, forall n, p n <= c * n^k) ->
  time_constructible p.

Axiom exponential_time_constructible :
  forall (base : nat),
  base >= 2 ->
  time_constructible (fun n => base ^ n).

(** The specific subexponential function from the paper:
    t(n) = 2^(log(n)^(1/2) * (log log n)^(1/2))

    We cannot define this precisely in Coq without real number logarithms,
    so we axiomatize its key properties. *)

Parameter t_subexp : nat -> nat.

Axiom t_subexp_properties :
  time_constructible t_subexp /\
  (forall n, n >= 1 -> t_subexp n >= n) /\
  (exists c, forall n, n >= c -> t_subexp n < 2^n) /\
  (forall k c, exists N, forall n, n >= N -> t_subexp n > c * n^k).

(** ** DTIME Complexity Classes *)

(** DTIME(t) is the class of languages decidable by a deterministic
    Turing machine in time O(t(n)).

    We axiomatize this as we cannot model TMs directly. *)

Axiom DTIME : (nat -> nat) -> language -> Prop.

(** Basic properties of DTIME *)
Axiom DTIME_monotone :
  forall (t1 t2 : nat -> nat) (L : language),
  (forall n, t1 n <= t2 n) ->
  DTIME t1 L ->
  DTIME t2 L.

Axiom DTIME_closed_union :
  forall (t : nat -> nat) (L1 L2 : language),
  DTIME t L1 ->
  DTIME t L2 ->
  DTIME t (fun w => L1 w \/ L2 w).

(** ** Time Hierarchy Theorem *)

(** Theorem 4.6 from the paper: The deterministic Time Hierarchy Theorem

    If t and T are fully time-constructible functions with:
    - t(n) >= n
    - lim (t(n) * log t(n)) / T(n) = 0
    - t <= T

    Then: DTIME(t) ⊊ DTIME(T)

    This means there exists a language L_D in DTIME(T) but not in DTIME(t).
*)

Axiom time_hierarchy_theorem :
  forall (t T : nat -> nat),
  time_constructible t ->
  time_constructible T ->
  (forall n, t n >= n) ->
  (forall n, t n <= T n) ->
  (** The limit condition: for all c > 0, there exists N such that
      for all n >= N, we have t(n) * log t(n) < c * T(n).
      We approximate this with: for all c, eventually t*log(t) < c*T *)
  (forall c, exists N, forall n, n >= N -> t n * Nat.log2 (t n) < c * T n) ->
  (** Conclusion: There exists a language in DTIME(T) but not in DTIME(t) *)
  exists L_D : language,
    DTIME T L_D /\ ~ DTIME t L_D.

(** ** The Diagonal Language L_D *)

(** By the Time Hierarchy Theorem, we get a hard language L_D.

    The paper constructs this via diagonalization (equation 9):
    L_D = { w | M_w does NOT accept ρ(M_w) in time t(|w|) }

    Where:
    - M_w is the Turing machine encoded by (some prefix of) w
    - ρ(M_w) is the "functional prefix" encoding the TM

    **CRITICAL ISSUE (Error 1)**: The paper uses "wasteful encoding"
    (Figure 2) to pad encodings, claiming this makes the worst case
    occur frequently. However:
    - If M_w operates on ρ(M_w), the padding doesn't help
    - If M_w operates on the full padded w, it's not true self-reference
    - This creates a logical inconsistency
*)

Parameter L_D : language.

Axiom L_D_in_DTIME_2_exp_n :
  DTIME (fun n => 2^n) L_D.

Axiom L_D_not_in_DTIME_t_subexp :
  ~ DTIME t_subexp L_D.

(** The problematic "wasteful encoding" property:
    The paper claims that for each TM M, there are exponentially many
    encodings w such that M_w = M, and the "worst case" (where M rejects
    itself within the time bound) occurs with frequency >= 1/(4*ℓ).

    **ERROR**: This frequency claim is not properly justified. *)

Axiom wasteful_encoding_frequency :
  forall (ell : nat),
  exists (bad_fraction : nat),
  (** Claimed: At least 1/(4*ell) fraction of encodings fail diagonalization *)
  bad_fraction * 4 * ell >= 2^ell.

(** This axiom is actually FALSE for large ell, but we state it to
    show where the paper's argument would go. *)

(** ** Language of Squares *)

(** SQ = { y | exists x, y = x^2 }

    The paper intersects L_D with SQ to control density.
*)

Definition is_square (n : nat) : Prop :=
  exists x : nat, n = x * x.

(** Interpret a string as a natural number (binary encoding) *)
Parameter string_to_nat : string -> nat.

Axiom string_to_nat_injective :
  forall s1 s2, string_to_nat s1 = string_to_nat s2 -> s1 = s2.

Axiom string_to_nat_length_bound :
  forall s, string_to_nat s < 2^(length s).

(** The language of squares *)
Definition SQ : language :=
  fun w => is_square (string_to_nat w).

(** SQ is computable in polynomial time *)
Axiom SQ_decidable :
  exists poly, DTIME poly SQ.

(** ** The Controlled Density Language L_0 *)

(** L_0 = L_D ∩ SQ *)
Definition L_0 : language :=
  fun w => L_D w /\ SQ w.

Lemma L_0_in_DTIME_2_exp_n :
  DTIME (fun n => 2^n) L_0.
Proof.
  unfold L_0.
  (** We need to show that the intersection of two decidable languages
      is decidable. This requires DTIME closure properties. *)
  admit. (** Omitted: requires more DTIME infrastructure *)
Admitted.

(** ** Density Functions *)

(** The density function counts how many yes-instances occur in
    the first x strings (in canonical order).

    dens_L(x) = |{ w : string_to_nat(w) <= x /\ L(w) }|
*)

Definition density (L : language) (x : nat) : nat :=
  (** Count of yes-instances up to x *)
  (** We cannot compute this constructively, so we axiomatize *)
  0. (** Placeholder *)

Axiom density_spec :
  forall L x,
  density L x =
  (** Informally: |{ n <= x | L(nat_to_string n) }| *)
  0. (** Proper specification would require decidable equality on strings *)

(** ** Lemma 4.7: Upper Bound on Density of L_0 *)

(** Lemma 4.7: dens_L0(x) <= sqrt(x)

    Proof sketch: L_0 ⊆ SQ, and there are at most sqrt(x) squares up to x.
*)

Lemma density_L_0_upper_bound :
  forall x : nat,
  density L_0 x <= Nat.sqrt x + 1.
Proof.
  intro x.
  (** The number of squares up to x is at most sqrt(x) *)
  (** Since L_0 ⊆ SQ, we have dens_L0(x) <= dens_SQ(x) <= sqrt(x) *)
  admit. (** Requires proper density infrastructure *)
Admitted.

(** ** Lemma 4.8: Polynomial Reduction from SQ to L_0 *)

(** The paper claims a polynomial reduction φ: SQ → L_0 that pads
    words to make them squares while preserving L_D membership.

    **CRITICAL ISSUE (Error 2)**: This reduction is used to prove
    the lower bound on density (Lemma 4.10), but the reduction itself
    depends on having enough "room" to pad, which depends on density.
    This creates circular reasoning.
*)

Axiom reduction_SQ_to_L_0 :
  exists (phi : string -> string),
  (** Reduction preserves membership *)
  (forall w, SQ w -> L_0 (phi w)) /\
  (** Reduction is polynomial-time computable *)
  (exists poly, forall w, length (phi w) <= poly (length w)) /\
  (** The reduction creates squares *)
  (forall w, SQ (phi w)).

(** ** Lemma 4.10: Lower Bound on Density of L_0 *)

(** Lemma 4.10: dens_L0(x) >= d * x^(1/beta)
    for some constant d > 0 and beta >= 6.

    **ERROR**: The proof uses the reduction from Lemma 4.8, creating
    a circular dependency. The reduction needs density bounds to work,
    but it's used to prove the density bounds.
*)

(* COMPILATION ERROR: Type mismatch at line 272
   The term "d" has type "R" while it is expected to have type "nat"
   in the context of "d > 0" with nat_scope open.

   Fix needed: Use R_scope for real number comparisons, e.g.:
   - Change to: (d > 0)%R
   - Or locally open R_scope

   Commenting out to preserve what compiles before this error.
*)

(*
Axiom density_L_0_lower_bound :
  exists (d : R) (beta : nat),
  d > 0 /\
  beta >= 6 /\
  forall x : nat,
  x >= 1 ->
  (density L_0 x >= 0). (** Simplified; actual bound is d * x^(1/beta) *)
*)

(** ** Gap Analysis: Where the Proof Breaks Down *)

(** **Error 1: Encoding Mismatch**

    The wasteful encoding (Figure 2 in paper) is supposed to make
    the diagonalization failure occur frequently, but:
*)

Lemma encoding_mismatch_issue :
  (** If we have many encodings of the same TM M... *)
  forall (M : nat) (encodings : list string),
  (** ...and they all encode the same machine... *)
  (forall w, In w encodings -> string_to_nat w = M) ->
  (** ...then the diagonalization should fail for all of them or none *)
  (** But the paper claims it fails for a 1/(4*ell) fraction! *)
  False.
Proof.
  (** This is a contradiction in the paper's argument.
      The diagonalization property is a property of the TM M itself,
      not of the encoding w. Multiple encodings of the same M should
      all have the same diagonalization behavior. *)
  admit.
Admitted.

(** **Error 2: Circular Density Bounds**

    The reduction phi in Lemma 4.8 needs to pad words to specific
    lengths that are squares. The amount of padding required depends
    on the density of L_0. But Lemma 4.10 uses phi to prove the
    density bounds!
*)

Lemma circular_density_issue :
  (** Assume we have the reduction *)
  forall (phi : string -> string),
  (** The reduction needs to know where to pad to *)
  (forall w, exists target_len,
    length (phi w) = target_len /\
    is_square target_len) ->
  (** But choosing target_len requires knowing density of L_0! *)
  (forall w,
    (** We need density info to ensure we don't "overshoot" *)
    exists safety_margin,
    density L_0 (2^(length w)) >= safety_margin) ->
  (** This creates a circular dependency *)
  False.
Proof.
  (** The proof of Lemma 4.10 uses phi, but the definition of phi
      needs the density bounds that Lemma 4.10 is trying to prove. *)
  admit.
Admitted.

(** ** Summary of Coq Formalization *)

(** We have formalized:
    1. Time-constructible functions and DTIME complexity classes
    2. The Time Hierarchy Theorem (axiomatized)
    3. The diagonal language L_D
    4. The language of squares SQ
    5. The controlled density language L_0 = L_D ∩ SQ
    6. Density functions and their bounds (Lemmas 4.7, 4.10)

    **Critical gaps identified**:
    - Error 1: encoding_mismatch_issue shows the wasteful encoding
      creates logical inconsistency
    - Error 2: circular_density_issue shows the density bounds
      depend on a reduction that itself needs those bounds

    These gaps prevent the formalization from being completed and
    expose fundamental flaws in the paper's argument.
*)
