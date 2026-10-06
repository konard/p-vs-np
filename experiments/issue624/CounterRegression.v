From Stdlib Require Import List Bool Arith.
From proofs.experiments.issue624.rocq Require Import UnaryCounter.
Import ListNotations Complexity.Complexity Machines UnaryCounter.

Example generic_counter : forall (x : Word) (l : list Symbol) (k : nat),
  Reaches counter (cursor l x k) (countTime (length x) k) (finished l x k).
Proof. intros. apply counter_reaches. Qed.

Fixpoint probe (m : Machine) (fuel : nat) (c : Config) : option Config :=
  match fuel with
  | 0 => None
  | S f => if Nat.eqb (state c) (length (program m)) then Some c else
    match step m c with inl _ => None | inr d => probe m f d end
  end.
Definition result (x : Word) (l : list Symbol) (k : nat) :=
  option_map (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
    (probe counter (S (countTime (length x) k)) (cursor l x k)).
Example fixed_states : length (program counter) = 9. Proof. reflexivity. Qed.
Example empty_cost : countTime 0 0 = 2. Proof. reflexivity. Qed.
Example empty : result [] [] 0 = Some (9, [], blank, [separator]). Proof. reflexivity. Qed.
Example zero_bit : result [false] [] 0 = Some (9, [zero], blank, [separator; one]).
Proof. reflexivity. Qed.
Example mixed : result [true; false; true] [separator] 2 =
  Some (9, [one; zero; one; separator], blank, [separator; one; one; one; one; one]).
Proof. reflexivity. Qed.
Example retained_prefix : result [] [one; zero] 3 =
  Some (9, [one; zero], blank, [separator; one; one; one]). Proof. reflexivity. Qed.
Example insufficient_fuel : probe counter (countTime 3 2) (cursor [] [true; false; true] 2) = None.
Proof. reflexivity. Qed.
Example missing_separator : step counter
  {| state := 1; tapeLeft := []; tapeHead := blank; tapeRight := [] |} = inl false.
Proof. reflexivity. Qed.
Example invalid_counter : step counter
  {| state := 6; tapeLeft := []; tapeHead := zero; tapeRight := [] |} = inl false.
Proof. reflexivity. Qed.
Example polynomial_cost : forall n k,
  countTime n k <= evalPoly counterPolynomial (n + k).
Proof. exact countTime_polynomial. Qed.
Print Assumptions counter_reaches.
Print Assumptions countTime_polynomial.
Example real_input : forall x,
  Reaches countedInput (initial x) (inputTime (length x)) (shiftConfig 7 (finished [] x 0)).
Proof. exact countedInput_reaches. Qed.
Definition fromInput (x : Word) :=
  option_map (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
    (probe countedInput (S (inputTime (length x))) (initial x)).
Example input_states : length (program countedInput) = 16. Proof. reflexivity. Qed.
Example real_empty : fromInput [] = Some (16, [], blank, [separator]). Proof. reflexivity. Qed.
Example real_mixed : fromInput [false; true; false] =
  Some (16, [zero; one; zero], blank, [separator; one; one; one]). Proof. reflexivity. Qed.
Example real_one : fromInput [true] = Some (16, [one], blank, [separator; one]).
Proof. reflexivity. Qed.
Print Assumptions prepare_reaches.
Print Assumptions countedInput_reaches.
Print Assumptions inputTime_polynomial.
