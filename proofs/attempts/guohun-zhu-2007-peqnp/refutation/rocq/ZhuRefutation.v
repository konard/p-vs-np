(* Finite projector witness for Zhu (2007), Lemma 4.
   See the adjacent README for the scope of the code-permutation quotient. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module ZhuRefutation.

Definition vertices := seq 0 6.
Definition arc (u v : nat) : bool :=
  Nat.eqb (v / 2) ((u / 2 + 1) mod 3).

(* A projector edge u+--v- corresponds exactly to an arc u -> v. *)
Definition projector_edge := arc.

Definition left_component (u : nat) := u / 2.
Definition right_component (v : nat) := (v / 2 + 2) mod 3.

(* Three complete bipartite 2-by-2 components, hence three C4 cycles. *)
Definition component_edges_hold : bool :=
  forallb (fun u => forallb (fun v =>
    Bool.eqb (projector_edge u v)
      (Nat.eqb (left_component u) (right_component v))) vertices)
    vertices.

Theorem projector_component_edges : component_edges_hold = true.
Proof. vm_compute; reflexivity. Qed.

Definition component_sizes_hold : bool :=
  forallb (fun c =>
    Nat.eqb (length (filter (fun u =>
      Nat.eqb (left_component u) c) vertices)) 2 &&
    Nat.eqb (length (filter (fun v =>
      Nat.eqb (right_component v) c) vertices)) 2) (seq 0 3).

Theorem projector_component_sizes : component_sizes_hold = true.
Proof. vm_compute; reflexivity. Qed.

Definition matching (a b c : bool) (u : nat) : nat :=
  match u with
  | 0 => if a then 3 else 2
  | 1 => if a then 2 else 3
  | 2 => if b then 5 else 4
  | 3 => if b then 4 else 5
  | 4 => if c then 1 else 0
  | _ => if c then 0 else 1
  end.

Definition perfect (m : nat -> nat) : bool :=
  forallb (fun u => projector_edge u (m u)) vertices &&
  Nat.eqb (length (nodup Nat.eq_dec (map m vertices))) 6.

Theorem all_codes_perfect :
  forall a b c, perfect (matching a b c) = true.
Proof.
  intros [] [] []; vm_compute; reflexivity.
Qed.

Definition degree_two_out : bool :=
  forallb (fun u =>
    Nat.eqb (length (filter (arc u) vertices)) 2) vertices.
Definition degree_two_in : bool :=
  forallb (fun v =>
    Nat.eqb (length (filter (fun u => arc u v) vertices)) 2) vertices.

Definition reach3 (u v : nat) : bool :=
  Nat.eqb u v || arc u v ||
  existsb (fun w => arc u w && arc w v) vertices ||
  existsb (fun w =>
    existsb (fun z => arc u w && arc w z && arc z v) vertices) vertices.

Theorem valid_gamma_input :
  degree_two_out = true /\ degree_two_in = true /\
  forallb (fun u => forallb (reach3 u) vertices) vertices = true.
Proof. vm_compute; auto. Qed.

(* Theorem 1(c3) says at most n/4 C4 components, where n=|V(D)|.
   This single proposition includes the Γ conditions, the three complete
   2-by-2 projector components, and the failed inequality 3 > 6/4. *)
Theorem theorem1_c3_counterexample :
  degree_two_out = true /\ degree_two_in = true /\
  forallb (fun u => forallb (reach3 u) vertices) vertices = true /\
  component_edges_hold = true /\ component_sizes_hold = true /\
  3 > 6 / 4.
Proof.
  pose proof valid_gamma_input as [Hout [Hin Hreach]].
  repeat split; try assumption; try apply projector_component_edges;
    try apply projector_component_sizes; vm_compute; lia.
Qed.

Definition weight (a b c : bool) : nat :=
  (if a then 1 else 0) + (if b then 1 else 0) +
  (if c then 1 else 0).

Theorem four_code_classes :
  weight false false false = 0 /\
  weight true false false = 1 /\
  weight true true false = 2 /\
  weight true true true = 3 /\
  6 / 2 < 4.
Proof. vm_compute; auto. Qed.

Fixpoint orbit (m : nat -> nat) (k : nat) : nat :=
  match k with 0 => 0 | S j => m (orbit m j) end.

Definition one_cycle (m : nat -> nat) : bool :=
  forallb (fun v =>
    existsb (fun k => Nat.eqb (orbit m k) v) vertices) vertices.

Theorem different_cycle_outcomes :
  one_cycle (matching false false false) = false /\
  one_cycle (matching true false false) = true.
Proof. vm_compute; auto. Qed.

End ZhuRefutation.
