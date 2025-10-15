(**
  PSubsetNP.v - Formal proof that P ⊆ NP

  This file provides a formal proof of the well-known inclusion P ⊆ NP,
  which states that every language decidable in polynomial time is also
  verifiable in polynomial time with a certificate.

  This is a fundamental result in computational complexity theory.
*)

Require Import Coq.Strings.String.
Open Scope string_scope.

(** * 1. Basic Definitions *)

(** A language is a decision problem over strings *)
Definition Language := string -> bool.

(** Time complexity: maps input size to maximum number of steps *)
Definition TimeComplexity := nat -> nat.

(** Polynomial time: there exist constants c and k such that T(n) <= c * n^k *)
Definition isPolynomial (T : TimeComplexity) : Prop :=
  exists (c k : nat), forall n : nat, T n <= c * n ^ k.

(** * 2. Complexity Classes *)

(** Class P: Languages decidable in polynomial time *)
Record ClassP : Type := mkClassP {
  p_language : Language;
  p_decider : string -> nat;  (* Simplified: returns number of steps *)
  p_timeComplexity : TimeComplexity;
  p_isPoly : isPolynomial p_timeComplexity;
  p_correct : forall s : string, p_language s = match p_decider s with 0 => false | _ => true end
}.

(** Class NP: Languages with polynomial-time verifiable certificates *)
Record ClassNP : Type := mkClassNP {
  np_language : Language;
  np_verifier : string -> string -> bool;  (* (input, certificate) -> acceptance *)
  np_timeComplexity : TimeComplexity;
  np_isPoly : isPolynomial np_timeComplexity;
  np_correct : forall s : string, np_language s = true <-> exists cert : string, np_verifier s cert = true
}.

(** * 3. Main Theorem: P ⊆ NP *)

(**
  Theorem: P ⊆ NP

  Every language in P is also in NP. This is proven by constructing an NP verifier
  that ignores the certificate and directly uses the P decider.
*)
Theorem pSubsetNP : forall L : ClassP, exists L' : ClassNP,
  forall s : string, p_language L s = np_language L' s.
Proof.
  intro L.
  (* Construct an NP machine that ignores the certificate *)
  assert (correct_prop: forall s : string,
    p_language L s = true <-> exists cert : string, p_language L s = true).
  {
    intro s. split.
    - intro H. exists EmptyString. exact H.
    - intro H. destruct H as [cert H]. exact H.
  }
  exists (mkClassNP
    (p_language L)
    (fun s _ => p_language L s)  (* Verifier ignores certificate *)
    (p_timeComplexity L)
    (p_isPoly L)
    correct_prop
  ).
  intro s.
  reflexivity.
Qed.

(** * 4. Verification *)

Check pSubsetNP.

(**
  Summary: We have formally proven that P ⊆ NP, a fundamental result
  in computational complexity theory showing that polynomial-time decidable
  languages are also polynomial-time verifiable.
*)
