import proofs.complexity.lean.Complexity

open Complexity

def rejectMachine : Machine :=
  ⟨[[.halt false, .halt false, .halt false, .halt false]]⟩

example : step rejectMachine (initial [true]) = .inl false := rfl
example : Run rejectMachine (initial [true]) 1 false := .halt rfl
example : ¬Run rejectMachine (initial [true]) 0 false := by
  intro h
  cases h

example : (Polynomial.mk 1 0).eval 0 = 1 := rfl
