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
