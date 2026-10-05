From Stdlib Require Import List Bool Arith.
From proofs.experiments.issue624.rocq Require Import ConstantEmitter.
Import ListNotations Complexity.Complexity Machines ConstantEmitter.

Example computed_word : forall w,
  Computes (emitter w) (fun _ => w) (emitterPolynomial w).
Proof. apply emitter_computes. Qed.
Example empty_clause_output :
  Computes (emitter (encodeCNF [[]])) (fun _ => encodeCNF [[]])
    (emitterPolynomial (encodeCNF [[]])).
Proof. apply emitter_computes. Qed.
Example empty_output : Computes (emitter []) (fun _ => []) (emitterPolynomial []).
Proof. apply emitter_computes. Qed.
Example empty_states : length (program (emitter [])) = 4.
Proof. reflexivity. Qed.
Example two_bit_states : length (program (emitter [true; false])) = 8.
Proof. reflexivity. Qed.

Fixpoint probe (m : Machine) (fuel : nat) (c : Config) : option Config :=
  match fuel with
  | 0 => None
  | S fuel => if Nat.eqb (state c) (length (program m)) then Some c else
    match step m c with
    | inl _ => None
    | inr d => probe m fuel d
    end
  end.
Definition probeWord (w x : Word) : option (list Symbol * list Symbol) :=
  option_map (fun c => (tapeLeft c, tapeHead c :: tapeRight c))
    (probe (emitter w) (evalPoly (emitterPolynomial w) (length x) + 1) (initial x)).

Example empty_probe : probeWord [] [] = Some ([], blanks 2).
Proof. reflexivity. Qed.
Example one_probe : probeWord [true] [] = Some ([], [one; blank]).
Proof. reflexivity. Qed.
Example shorter_output : probeWord [false; true] [true; false; true] =
  Some ([], [zero; one; blank; blank]).
Proof. reflexivity. Qed.
Example longer_output : probeWord [true; false; true] [false] =
  Some ([], [one; zero; one; blank]).
Proof. reflexivity. Qed.

Print Assumptions emitter_computes.
