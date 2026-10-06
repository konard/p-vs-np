import proofs.experiments.issue624.lean.UnaryCounter
open Complexity Issue532.Machines Issue624.UnaryCounter

-- The same nine-state block retains every input bit and increments the
-- existing unary counter once per bit. Both tape sides matter to this test.
example (x : Word) (l : List Symbol) (k : Nat) :
    Reaches counter (cursor l x k) (countTime x.length k)
      (finished l x k) := counter_reaches l x k

private def probe (m : Machine) : Nat → Config → Option Config
  | 0, _ => none
  | fuel + 1, c => if c.state = m.program.length then some c else
    match step m c with
    | .inl _ => none
    | .inr d => probe m fuel d

private def result (x : Word) (l : List Symbol) (k : Nat) :=
  (probe counter (countTime x.length k + 1) (cursor l x k)).map
    (fun c => (c.state, c.left, c.head, c.right))

example : counter.program.length = 9 := by decide
example : countTime 0 0 = 2 := by decide
example : result [] [] 0 = some (9, [], .blank, [.separator]) := by decide
example : result [false] [] 0 = some (9, [.zero], .blank, [.separator, .one]) := by decide
example : result [true, false, true] [.separator] 2 =
    some (9, [.one, .zero, .one, .separator], .blank,
      [.separator, .one, .one, .one, .one, .one]) := by decide
example : result [] [.one, .zero] 3 =
    some (9, [.one, .zero], .blank, [.separator, .one, .one, .one]) := by decide
example : probe counter (countTime 3 2) (cursor [] [true, false, true] 2) = none := by decide
example : step counter ⟨1, [], .blank, []⟩ = .inl false := rfl
example : step counter ⟨6, [], .zero, []⟩ = .inl false := rfl

example (n k : Nat) : countTime n k ≤ (counterPolynomial.eval (n + k)) :=
  countTime_polynomial n k

#print axioms counter_reaches
#print axioms countTime_polynomial

-- Entry from the real shared-model input, including a genuinely empty tape.
example (x : Word) : Reaches countedInput (initial x) (inputTime x.length)
    (shiftConfig 7 (finished [] x 0)) := countedInput_reaches x
private def fromInput (x : Word) :=
  (probe countedInput (inputTime x.length + 1) (initial x)).map
    (fun c => (c.state, c.left, c.head, c.right))
example : countedInput.program.length = 16 := by decide
example : fromInput [] = some (16, [], .blank, [.separator]) := by decide
example : fromInput [false, true, false] =
    some (16, [.zero, .one, .zero], .blank, [.separator, .one, .one, .one]) := by decide
example : fromInput [true] = some (16, [.one], .blank, [.separator, .one]) := by decide
#print axioms prepare_reaches
#print axioms countedInput_reaches
#print axioms inputTime_polynomial
