(* A collision for the raw truth-table polynomial in Groff (2011).
   This does not model his later coefficient transformations or reconstruction. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module GroffRefutation.

Definition assignments := seq 0 8.
Definition formula := list nat.

(* c encodes the full three-literal clause falsified only by assignment c. *)
Definition bit (a i : nat) : bool :=
  Nat.eqb ((a / (2 ^ i)) mod 2) 1.
Definition clause_satisfied (c a : nat) : bool :=
  existsb (fun i => negb (Bool.eqb (bit a i) (bit c i))) (seq 0 3).

Definition satisfies (f : formula) (a : nat) : bool :=
  forallb (fun c => clause_satisfied c a) f.

Definition sat_formula : formula := [1; 2; 4; 6; 7; 1; 2; 4].
Definition unsat_formula : formula := [0; 1; 2; 3; 4; 5; 6; 7].

Definition raw_value (f : formula) : nat :=
  fold_left (fun total i =>
    total + if satisfies f i then 3 ^ i else 0) assignments 0 mod 271.

Definition satisfying_count (f : formula) : nat :=
  length (filter (satisfies f) assignments).

Theorem field_and_input_conditions :
  (forallb (fun d => negb (Nat.eqb (271 mod d) 0)) (seq 2 15) = true) /\
  271 > (2 * length sat_formula) ^ 2 /\
  271 > (2 * length unsat_formula) ^ 2.
Proof. vm_compute; repeat split; try reflexivity; lia. Qed.

Theorem sat_and_unsat_inputs :
  length sat_formula = 8 /\
  length unsat_formula = 8 /\
  satisfies sat_formula 0 = true /\
  satisfying_count unsat_formula = 0.
Proof. vm_compute; repeat split; try reflexivity; lia. Qed.

Theorem raw_evaluation_collision :
  raw_value sat_formula = 0 /\
  raw_value unsat_formula = 0 /\
  satisfying_count sat_formula = 3 /\
  satisfying_count unsat_formula = 0.
Proof. vm_compute; repeat split; try reflexivity; lia. Qed.

End GroffRefutation.
