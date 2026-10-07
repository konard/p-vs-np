import proofs.experiments.issue624.lean.RegisterMachine
open Complexity Issue532.Machines Issue624.RegisterMachine

example (pre post : List Word) (w : Word) (b : Bool) :
    Reaches (push pre.length b) (home 0 (pre ++ w :: post))
      (pushTime (pre ++ w :: post))
      (home (push pre.length b).program.length (pre ++ (w ++ [b]) :: post)) :=
  push_reaches pre post w b

private def probe (m : Machine) : Nat → Config → Option Config
  | 0, _ => none
  | fuel + 1, c => if c.state = m.program.length then some c else
    match step m c with
    | .inl _ => none
    | .inr d => probe m fuel d

private def result (slot : Nat) (b : Bool) (blocks : List Word) :=
  (probe (push slot b) (pushTime blocks + 1) (home 0 blocks)).map
    (fun c => (c.state, c.left, c.head, c.right))

example : result 0 true [[], [], []] =
  some (6, [], .blank, [.one, .separator, .separator, .separator]) := by decide
example : result 1 true [[false, true], [], [true, false]] =
  some (7, [], .blank, [.zero, .one, .separator, .one, .separator,
    .one, .zero, .separator]) := by decide
example : result 2 false [[true], [true, true], [true, false]] =
  some (8, [], .blank, [.one, .separator, .one, .one, .separator,
    .one, .zero, .zero, .separator]) := by decide
example : probe (push 1 true) (pushTime [[false], [], [true]])
  (home 0 [[false], [], [true]]) = none := by decide
example : step (push 0 true) ⟨0, [], .one, []⟩ = .inl false := rfl
#print axioms push_reaches

example (pre post : List Word) (old w : Word) :
    Reaches (pushWord pre.length w) (home 0 (pre ++ old :: post))
      (wordTime w.length (tape (pre ++ old :: post)).length)
      (home (pushWord pre.length w).program.length (pre ++ (old ++ w) :: post)) :=
  pushWord_reaches pre post old w

private def fromState (m : Machine) (x : Word) (st : State) (count : Nat) :=
  (probe m (wordTime count (tape (blocks x st)).length + 1) (encode 0 x st)).map
    (fun c => (c.state, c.left, c.head, c.right))
example : fromState (incr 1 2) [false, true] ⟨[1, 0, 1], [false]⟩ 2 =
    some (16, [], .blank, [.zero, .one, .separator, .one, .separator,
      .one, .one, .separator, .one, .separator, .zero, .separator]) := by decide
example : fromState (emitConst 2 [true, false]) [false] ⟨[0, 1], [true]⟩ 2 =
    some (18, [], .blank, [.zero, .separator, .separator, .one, .separator,
      .one, .one, .zero, .separator]) := by decide
example : fromState (emitConst 0 []) [true] ⟨[], [false]⟩ 0 =
    some (0, [], .blank, [.one, .separator, .zero, .separator]) := by decide
example (count size : Nat) : wordTime count size ≤ emissionPolynomial.eval (size+count) :=
  wordTime_polynomial count size
#print axioms pushWord_reaches
#print axioms incr_reaches
#print axioms emitConst_reaches
#print axioms wordTime_polynomial

private def composed : Prog := .seq (.increment 0 2) (.seq (.emit [false]) (.increment 1 1))
example : WellFormed 2 composed := by decide
example : cost [true] composed ⟨[0, 1], [true]⟩ = 84 := by decide
example : ((probe (compile 2 composed) 85 (encode 0 [true] ⟨[0, 1], [true]⟩)).map
    (fun c => (c.state, c.left, c.head, c.right))) =
    some (31, [], .blank, [.one, .separator, .one, .one, .separator,
      .one, .one, .separator, .one, .zero, .separator]) := by decide
example (x : Word) (k : Nat) (p : Prog) (st : State) (hp : WellFormed k p)
    (hs : st.regs.length = k) :
    Reaches (compile k p) (encode 0 x st) (cost x p st)
      (encode (compile k p).program.length x (runProg p st)) :=
  compile_reaches x k p st hp hs

example : ¬ WellFormed 0 (.increment 0 1) := by decide
example : probe (compile 2 composed) 84 (encode 0 [true] ⟨[0, 1], [true]⟩) = none := by decide
example : probe (compile 2 .empty) 1 (encode 0 [] ⟨[0, 1], []⟩) =
    some (encode 0 [] ⟨[0, 1], []⟩) := rfl
example (x : Word) (k : Nat) (p : Prog) (st : State) (hp : WellFormed k p)
    (hs : st.regs.length = k) :
    cost x p st ≤ emissionPolynomial.eval ((tape (blocks x st)).length + growth p) :=
  cost_polynomial x k p st hp hs
#print axioms compile_reaches
#print axioms cost_eq_wordTime
#print axioms cost_polynomial

-- Destructive unary registers must retain both surrounding blocks.
example (pre post : List Word) (n : Nat) :
    ∃ c, Reaches (clear pre.length) (home 0 (pre ++ List.replicate n true :: post))
      (clearTime (tape pre).length n (tape post).length) c ∧
      Similar (home (clear pre.length).program.length (pre ++ [] :: post)) c :=
  clear_reaches pre post n
example : ((probe (clear 1) 200 (home 0 [[false, true], [true, true], [true, false]])).map
    (fun c => (c.state, c.left, c.head, c.right))) =
    some (11, [], .blank, [.zero, .one, .separator, .separator,
      .one, .zero, .separator, .blank, .blank, .blank]) := by decide
example : ((probe (clear 1) 20 (home 0 [[], [], []])).map
    (fun c => c.right)) = some [.separator, .separator, .separator] := by decide
example : step (clear 0) ⟨0, [], .one, []⟩ = .inl false := rfl
#print axioms clear_reaches
example : probe (clear 1) 100 (home 0 [[true], [true, false], []]) = none := by decide

-- Clearing is consumed by charged compilation, including residual blanks.
private def afterClear : Prog := .seq (.increment 0 1) (.emit [false])
example : ((probe (clearThen 0 1 afterClear) 200
    (encode 0 [true] ⟨[2], [true]⟩)).map
    (fun c => (c.state, c.left, c.head, c.right))) =
    some (26, [], .blank, [.one, .separator, .one, .separator,
      .one, .zero, .separator, .blank]) := by decide
example (x : Word) (pre post : List Nat) (value : Nat) (out : Word) (k : Nat)
    (p : Prog) (hp : WellFormed k p) (hk : (pre ++ 0 :: post).length = k) :
    ∃ c, Reaches (clearThen pre.length k p) (encode 0 x ⟨pre ++ value :: post, out⟩)
      (clearTime (tape (x :: regWords pre)).length value
        (tape (regWords post ++ [out])).length + cost x p ⟨pre ++ 0 :: post, out⟩) c ∧
      Similar (encode (clearThen pre.length k p).program.length x
        (runProg p ⟨pre ++ 0 :: post, out⟩)) c :=
  clear_then_compile_reaches x pre post value out k p hp hk
example : clearTime 2 2 2 + cost [true] afterClear ⟨[0], [true]⟩ = 83 := by decide
example : probe (clearThen 0 1 afterClear) 83 (encode 0 [true] ⟨[2], [true]⟩) = none := by decide
#print axioms clear_then_compile_reaches
#print axioms clearTime_polynomial
example (x : Word) (pre post : List Nat) (value : Nat) (out : Word) (k : Nat)
    (p : Prog) (hp : WellFormed k p) (hk : (pre ++ 0 :: post).length = k) :
    clearTime (tape (x :: regWords pre)).length value
        (tape (regWords post ++ [out])).length + cost x p ⟨pre ++ 0 :: post, out⟩ ≤
      (polyAdd clearPolynomial emissionPolynomial).eval
        ((tape (blocks x ⟨pre ++ value :: post, out⟩)).length + growth p) :=
  clear_then_cost_polynomial x pre post value out k p hp hk
#print axioms clear_then_cost_polynomial

-- A dynamic controller must repeat a fixed body, consume its unary counter,
-- retain the input and charge the backward jump on every iteration.
example : ((probe (repeatMachine 1 (emitConst 1 [true, true])) 300
    (encode 0 [false, true] ⟨[2], [false]⟩)).map
    (fun c => (c.state, c.left, c.head, c.right.take 10))) =
    some (28, [], .blank, [.zero, .one, .separator, .separator,
      .zero, .one, .one, .one, .one, .separator]) := by decide
example : ((probe (repeatMachine 1 (emitConst 1 [true, true])) 20
    (encode 0 [] ⟨[0], []⟩)).map (fun c => c.right)) =
    some [.separator, .separator, .separator] := by decide

example : probe (emitTicks 1 0) 149 (encode 0 [false, true] ⟨[2], [false]⟩) = none := by decide
example : ticksTime 3 2 2 = 149 := by decide
example : ¬ ReadOnly 0 (.seq (.emit [true]) (.increment 0 1)) := by simp [ReadOnly]
example : repeatRun 0 (.increment 1 1) 2 ⟨[2, 1], []⟩ = ⟨[0, 3], []⟩ := rfl
example : probe (repeatMachine 1 (compile 1 (.emit [true]))) 100
    (home 0 [[true], [true, false], []]) = none := by decide
example (x : Word) (k slot : Nat) (p : Prog) (hp : WellFormed k p) (hro : ReadOnly slot p)
    (hslot : slot < k) (n : Nat) (st : State) (hk : st.regs.length = k) (hn : registerAt slot st = n) :
    ∃ c, Reaches (repeatMachine (slot+1) (compile k p)) (encode 0 x st)
      (repeatCost x slot p n st) c ∧
      Similar (encode (repeatMachine (slot+1) (compile k p)).program.length x (repeatRun slot p n st)) c :=
  repeat_compile_reaches x k slot p hp hro hslot n st hk hn
example (pre value post : Nat) : ticksTime pre value post ≤ ticksPolynomial.eval (pre+value+post) :=
  ticksTime_polynomial pre value post
#print axioms repeat_compile_reaches
#print axioms emitTicks_reaches
#print axioms ticksTime_polynomial

-- Consume dynamic ticks with the shared literal delimiter and polarity.
example : literalTime 3 2 2 = 199 := by decide
example : ((probe (emitLiteral 1 0 false) 200
    (encode 0 [false, true] ⟨[2], [false]⟩)).map
    (fun c => (c.state, c.left, c.head, c.right.take 12))) =
    some (44, [], .blank, [.zero, .one, .separator, .separator,
      .zero, .one, .one, .one, .one, .zero, .zero, .separator]) := by decide
example : ((probe (emitLiteral 1 0 true) 30 (encode 0 [] ⟨[0], []⟩)).map
    (fun c => c.right.take 5)) =
    some [.separator, .separator, .zero, .one, .separator] := by decide
example : probe (emitLiteral 1 0 false) 199 (encode 0 [false, true] ⟨[2], [false]⟩) = none := by decide
example (x : Word) (pre post : List Nat) (n : Nat) (out : Word) (pos : Bool) :
    ∃ c, Reaches (emitLiteral (pre ++ n :: post).length pre.length pos)
      (encode 0 x ⟨pre ++ n :: post, out⟩)
      (literalTime (tape (x :: regWords pre)).length n (tape (regWords post ++ [out])).length) c ∧
      Similar (encode (emitLiteral (pre ++ n :: post).length pre.length pos).program.length x
        ⟨pre ++ 0 :: post, out ++ encodeLit ⟨n, pos⟩⟩) c :=
  emitLiteral_reaches x pre post n out pos
example (pre value post : Nat) : literalTime pre value post ≤ literalPolynomial.eval (pre+value+post) :=
  literalTime_polynomial pre value post
#print axioms compose_home_reaches
#print axioms emitLiteral_reaches
#print axioms literalTime_polynomial
example (pre post : List Nat) (n m : Nat) (pos : Bool) :
    emitLiteral (pre ++ n :: post).length pre.length pos =
      emitLiteral (pre ++ m :: post).length pre.length pos := by simp
