From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import RegisterMachine.
Import ListNotations Complexity.Complexity Machines RegisterMachine.

Definition nestedProgram : Program :=
  loop 0 (sequence (straight (increment 1 2)) (loop 1 (straight (emit [true; false])))).
Example nested_well_formed : ProgramWellFormed 2 nestedProgram.
Proof. cbn; repeat split; lia. Qed.
Example nested_semantics : programRun nestedProgram (mkState [2; 0] [false]) =
  mkState [0; 0] [false; true; false; true; false; true; false; true; false].
Proof. reflexivity. Qed.
Example generic_nested_compiler : forall x k p st,
  ProgramWellFormed k p -> length (regs st) = k ->
  exists c, Reaches (compileProgram k p) (encode 0 x st) (programCost x p st) c /\
    Similar (encode (length (program (compileProgram k p))) x (programRun p st)) c.
Proof. exact compileProgram_reaches. Qed.
Example writing_counter_rejected : ~ ProgramWellFormed 1 (loop 0 (straight (increment 0 1))).
Proof. cbn; tauto. Qed.
Example clearing_counter_rejected : ~ ProgramWellFormed 1 (loop 0 (clearRegister 0)).
Proof. cbn; tauto. Qed.
Example emitting_counter_rejected : ~ ProgramWellFormed 1 (loop 0 (literal 0 true)).
Proof. cbn; tauto. Qed.
Example nested_counter_rejected : ~ ProgramWellFormed 1 (loop 0 (loop 0 (straight empty))).
Proof. cbn; tauto. Qed.
Example copy_well_formed : ProgramWellFormed 3 (addToProgram 0 1 2).
Proof. cbn; repeat split; lia. Qed.
Example copy_retains_source : programRun (addToProgram 0 1 2) (mkState [2; 3; 4] [false; true]) =
  mkState [2; 5; 0] [false; true].
Proof. reflexivity. Qed.
Example copy_reverse_slots : programRun (addToProgram 2 0 1) (mkState [1; 0; 3] [true; false]) =
  mkState [4; 0; 3] [true; false].
Proof. reflexivity. Qed.
Example copy_alias_rejected : ~ ProgramWellFormed 3 (addToProgram 0 0 2).
Proof. cbn; tauto. Qed.
Example copy_scratch_alias_rejected : ~ ProgramWellFormed 3 (addToProgram 0 1 0).
Proof. cbn; tauto. Qed.

Example generic_push : forall (pre post : list Word) (w : Word) (b : bool),
  Reaches (push (length pre) b) (home 0 (pre ++ w :: post))
    (pushTime (pre ++ w :: post))
    (home (length (program (push (length pre) b))) (pre ++ (w ++ [b]) :: post)).
Proof. exact push_reaches. Qed.

Fixpoint probe (m : Machine) (fuel : nat) (c : Config) : option Config :=
  match fuel with
  | 0 => None
  | S f => if Nat.eqb (state c) (length (program m)) then Some c else
    match step m c with inl _ => None | inr d => probe m f d end
  end.
Definition result (slot : nat) (b : bool) (blocks : list Word) :=
  option_map (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
    (probe (push slot b) (S (pushTime blocks)) (home 0 blocks)).
Definition programResult k p x st :=
  option_map (fun c => (state c, tapeLeft c, tapeHead c,
    firstn (length (tape (blocks x (programRun p st)))) (tapeRight c)))
    (probe (compileProgram k p) (S (programCost x p st)) (encode 0 x st)).
Example nested_execution : programResult 2 nestedProgram [] (mkState [1; 0] []) =
  Some (length (program (compileProgram 2 nestedProgram)), [], blank,
    tape (blocks [] (mkState [0; 0] [true; false; true; false]))).
Proof. reflexivity. Qed.
Example copy_execution : programResult 3 (addToProgram 0 1 2) [false] (mkState [1; 0; 1] [true]) =
  Some (length (program (compileProgram 3 (addToProgram 0 1 2))), [], blank,
    tape (blocks [false] (mkState [1; 1; 0] [true]))).
Proof. reflexivity. Qed.
Example copy_short_fuel : probe (compileProgram 3 (addToProgram 0 1 2))
  (programCost [false] (addToProgram 0 1 2) (mkState [1; 0; 1] [true]))
  (encode 0 [false] (mkState [1; 0; 1] [true])) = None.
Proof. reflexivity. Qed.
Example generic_copy_cost : forall x k source dest scratch st,
  length (regs st) = k -> source < k -> dest < k -> scratch < k ->
  source <> dest -> source <> scratch ->
  programCost x (addToProgram source dest scratch) st <=
    evalPoly copyPolynomial (length (tape (blocks x st))).
Proof. exact addToProgram_cost_polynomial. Qed.
Print Assumptions compileProgram_reaches.
Print Assumptions addToProgram_registers.
Print Assumptions addToProgram_reaches.
Print Assumptions addToProgram_cost_polynomial.
Example empty_blocks : result 0 true [[]; []; []] =
  Some (6, [], blank, [one; separator; separator; separator]).
Proof. reflexivity. Qed.
Example retained_suffix : result 1 true [[false; true]; []; [true; false]] =
  Some (7, [], blank, [zero; one; separator; one; separator; one; zero; separator]).
Proof. reflexivity. Qed.
Example final_output : result 2 false [[true]; [true; true]; [true; false]] =
  Some (8, [], blank, [one; separator; one; one; separator; one; zero; zero; separator]).
Proof. reflexivity. Qed.
Example insufficient_fuel : probe (push 1 true) (pushTime [[false]; []; [true]])
  (home 0 [[false]; []; [true]]) = None.
Proof. reflexivity. Qed.
Example missing_home : step (push 0 true)
  {| state := 0; tapeLeft := []; tapeHead := one; tapeRight := [] |} = inl false.
Proof. reflexivity. Qed.
Print Assumptions push_reaches.

Example generic_word : forall pre post old w,
  Reaches (pushWord (length pre) w) (home 0 (pre ++ old :: post))
    (wordTime (length w) (length (tape (pre ++ old :: post))))
    (home (length (program (pushWord (length pre) w))) (pre ++ (old ++ w) :: post)).
Proof. exact pushWord_reaches. Qed.
Definition fromState (m : Machine) (x : Word) (st : State) (count : nat) :=
  option_map (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
    (probe m (S (wordTime count (length (tape (blocks x st))))) (encode 0 x st)).
Example increment_middle : fromState (incr 1 2) [false; true] (mkState [1; 0; 1] [false]) 2 =
  Some (16, [], blank, [zero; one; separator; one; separator;
    one; one; separator; one; separator; zero; separator]).
Proof. reflexivity. Qed.
Example output_append : fromState (emitConst 2 [true; false]) [false] (mkState [0; 1] [true]) 2 =
  Some (18, [], blank, [zero; separator; separator; one; separator; one; one; zero; separator]).
Proof. reflexivity. Qed.
Example output_empty : fromState (emitConst 0 []) [true] (mkState [] [false]) 0 =
  Some (0, [], blank, [one; separator; zero; separator]).
Proof. reflexivity. Qed.
Example polynomial_cost : forall count size,
  wordTime count size <= evalPoly emissionPolynomial (size+count).
Proof. exact wordTime_polynomial. Qed.
Print Assumptions pushWord_reaches.
Print Assumptions incr_reaches.
Print Assumptions emitConst_reaches.
Print Assumptions wordTime_polynomial.

Definition composed : Prog := seq (increment 0 2) (seq (emit [false]) (increment 1 1)).
Example composed_well_formed : WellFormed 2 composed.
Proof. cbn; repeat split; auto. Qed.
Example composed_cost : cost [true] composed (mkState [0; 1] [true]) = 84.
Proof. reflexivity. Qed.
Example composed_execution : option_map
  (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
  (probe (compile 2 composed) 85 (encode 0 [true] (mkState [0; 1] [true]))) =
  Some (31, [], blank, [one; separator; one; one; separator;
    one; one; separator; one; zero; separator]).
Proof. reflexivity. Qed.
Example generic_compiler : forall x k p st, WellFormed k p -> length (regs st) = k ->
  Reaches (compile k p) (encode 0 x st) (cost x p st)
    (encode (length (program (compile k p))) x (runProg p st)).
Proof. exact compile_reaches. Qed.

Example invalid_register : ~ WellFormed 0 (increment 0 1).
Proof. cbn; lia. Qed.
Example composed_short_fuel : probe (compile 2 composed) 84
  (encode 0 [true] (mkState [0; 1] [true])) = None.
Proof. reflexivity. Qed.
Example empty_compiler : probe (compile 2 empty) 1 (encode 0 [] (mkState [0; 1] [])) =
  Some (encode 0 [] (mkState [0; 1] [])).
Proof. reflexivity. Qed.
Example generic_cost_bound : forall x k p st, WellFormed k p -> length (regs st) = k ->
  cost x p st <= evalPoly emissionPolynomial (length (tape (blocks x st)) + growth p).
Proof. exact cost_polynomial. Qed.
Print Assumptions compile_reaches.
Print Assumptions cost_eq_wordTime.
Print Assumptions cost_polynomial.

Example generic_clear : forall (pre post : list Word) n,
  exists c, Reaches (clear (length pre)) (home 0 (pre ++ repeat true n :: post))
    (clearTime (length (tape pre)) n (length (tape post))) c /\
    Similar (home (length (program (clear (length pre)))) (pre ++ [] :: post)) c.
Proof. exact clear_reaches. Qed.
Example clear_retained_suffix : option_map
  (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
  (probe (clear 1) 200 (home 0 [[false; true]; [true; true]; [true; false]])) =
  Some (11, [], blank, [zero; one; separator; separator;
    one; zero; separator; blank; blank; blank]).
Proof. reflexivity. Qed.
Example clear_empty : option_map tapeRight (probe (clear 1) 20 (home 0 [[]; []; []])) =
  Some [separator; separator; separator].
Proof. reflexivity. Qed.
Example clear_missing_home : step (clear 0)
  {| state := 0; tapeLeft := []; tapeHead := one; tapeRight := [] |} = inl false.
Proof. reflexivity. Qed.
Print Assumptions clear_reaches.
Example clear_malformed_unary : probe (clear 1) 100 (home 0 [[true]; [true; false]; []]) = None.
Proof. reflexivity. Qed.

Definition afterClear : Prog := seq (increment 0 1) (emit [false]).
Example clear_then_execution : option_map
  (fun c => (state c, tapeLeft c, tapeHead c, tapeRight c))
  (probe (clearThen 0 1 afterClear) 200 (encode 0 [true] (mkState [2] [true]))) =
  Some (26, [], blank, [one; separator; one; separator; one; zero; separator; blank]).
Proof. reflexivity. Qed.
Example generic_clear_compiler : forall x pre post value out k p,
  WellFormed k p -> length (pre ++ 0::post) = k ->
  exists c, Reaches (clearThen (length pre) k p) (encode 0 x (mkState (pre ++ value::post) out))
    (clearTime (length (tape (x::regWords pre))) value (length (tape (regWords post ++ [out]))) +
      cost x p (mkState (pre ++ 0::post) out)) c /\
    Similar (encode (length (program (clearThen (length pre) k p))) x
      (runProg p (mkState (pre ++ 0::post) out))) c.
Proof. exact clear_then_compile_reaches. Qed.
Example clear_then_cost : clearTime 2 2 2 + cost [true] afterClear (mkState [0] [true]) = 83.
Proof. reflexivity. Qed.
Example clear_then_short_fuel : probe (clearThen 0 1 afterClear) 83
  (encode 0 [true] (mkState [2] [true])) = None.
Proof. reflexivity. Qed.
Print Assumptions clear_then_compile_reaches.
Print Assumptions clearTime_polynomial.
Example generic_clear_cost_bound : forall x pre post value out k p,
  WellFormed k p -> length (pre ++ 0::post) = k ->
  clearTime (length (tape (x::regWords pre))) value (length (tape (regWords post ++ [out]))) +
    cost x p (mkState (pre ++ 0::post) out) <=
  evalPoly (polyAdd clearPolynomial emissionPolynomial)
    (length (tape (blocks x (mkState (pre ++ value::post) out))) + growth p).
Proof. exact clear_then_cost_polynomial. Qed.
Print Assumptions clear_then_cost_polynomial.

Example dynamic_repeat_execution : option_map
  (fun c => (state c, tapeLeft c, tapeHead c, firstn 10 (tapeRight c)))
  (probe (repeatMachine 1 (emitConst 1 [true; true])) 300
    (encode 0 [false; true] (mkState [2] [false]))) =
  Some (28, [], blank, [zero; one; separator; separator;
    zero; one; one; one; one; separator]).
Proof. reflexivity. Qed.
Example dynamic_repeat_empty : option_map tapeRight
  (probe (repeatMachine 1 (emitConst 1 [true; true])) 20
    (encode 0 [] (mkState [0] []))) = Some [separator; separator; separator].
Proof. reflexivity. Qed.

Example dynamic_ticks_short_fuel : probe (emitTicks 1 0) 149
  (encode 0 [false; true] (mkState [2] [false])) = None.
Proof. reflexivity. Qed.
Example dynamic_ticks_cost : ticksTime 3 2 2 = 149.
Proof. reflexivity. Qed.
Example invalid_loop_body : ~ ReadOnly 0 (seq (emit [true]) (increment 0 1)).
Proof. cbn; tauto. Qed.
Example dynamic_register_transfer : repeatRun 0 (increment 1 1) 2 (mkState [2; 1] []) = mkState [0; 3] [].
Proof. reflexivity. Qed.
Example malformed_loop_counter : probe (repeatMachine 1 (compile 1 (emit [true]))) 100
  (home 0 [[true]; [true; false]; []]) = None.
Proof. reflexivity. Qed.
Example generic_repeat_compiler : forall x k slot p, WellFormed k p -> ReadOnly slot p -> slot < k ->
  forall n st, length (regs st) = k -> registerAt slot st = n ->
  exists c, Reaches (repeatMachine (slot+1) (compile k p)) (encode 0 x st) (repeatCost x slot p n st) c /\
    Similar (encode (length (program (repeatMachine (slot+1) (compile k p)))) x (repeatRun slot p n st)) c.
Proof. exact repeat_compile_reaches. Qed.
Example generic_ticks_cost_bound : forall pre value post,
  ticksTime pre value post <= evalPoly ticksPolynomial (pre+value+post).
Proof. exact ticksTime_polynomial. Qed.
Print Assumptions repeat_compile_reaches.
Print Assumptions emitTicks_reaches.
Print Assumptions ticksTime_polynomial.

Example literal_cost : literalTime 3 2 2 = 199.
Proof. reflexivity. Qed.
Example literal_execution : option_map
  (fun c => (state c, tapeLeft c, tapeHead c, firstn 12 (tapeRight c)))
  (probe (emitLiteral 1 0 false) 200 (encode 0 [false; true] (mkState [2] [false]))) =
  Some (44, [], blank, [zero; one; separator; separator;
    zero; one; one; one; one; zero; zero; separator]).
Proof. reflexivity. Qed.
Example literal_zero_positive : option_map (fun c => firstn 5 (tapeRight c))
  (probe (emitLiteral 1 0 true) 30 (encode 0 [] (mkState [0] []))) =
  Some [separator; separator; zero; one; separator].
Proof. reflexivity. Qed.
Example literal_short_fuel : probe (emitLiteral 1 0 false) 199
  (encode 0 [false; true] (mkState [2] [false])) = None.
Proof. reflexivity. Qed.
Example generic_literal : forall x pre post n out pos,
  exists c, Reaches (emitLiteral (length (pre ++ n::post)) (length pre) pos)
    (encode 0 x (mkState (pre ++ n::post) out))
    (literalTime (length (tape (x::regWords pre))) n (length (tape (regWords post ++ [out])))) c /\
    Similar (encode (length (program (emitLiteral (length (pre ++ n::post)) (length pre) pos))) x
      (mkState (pre ++ 0::post) (out ++ encodeLit (mkLit n pos)))) c.
Proof. exact emitLiteral_reaches. Qed.
Example generic_literal_cost_bound : forall pre value post,
  literalTime pre value post <= evalPoly literalPolynomial (pre+value+post).
Proof. exact literalTime_polynomial. Qed.
Print Assumptions compose_home_reaches.
Print Assumptions emitLiteral_reaches.
Print Assumptions literalTime_polynomial.
Example literal_table_independent : forall (pre post : list nat) (n m : nat) (pos : bool),
  emitLiteral (length (pre ++ n::post)) (length pre) pos =
    emitLiteral (length (pre ++ m::post)) (length pre) pos.
Proof. intros. rewrite !length_app. cbn [length]. reflexivity. Qed.

Example subtraction_truncates :
  programRun (subProgram 0 1 2) (mkState [1; 2; 9; 4; 5] [false; true]) =
  mkState [1; 2; 0; 0; 0] [false; true].
Proof. reflexivity. Qed.
