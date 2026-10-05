import proofs.experiments.issue626.lean.Simulation

open Complexity Issue532.Circuits Issue626.Simulation

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

example (m : Machine) (p : Polynomial) (n : Nat) (hn : 0 < n) :
    WF n (simCircuit m p n) := simCircuit_WF m p n hn
example (m : Machine) (p : Polynomial) (n : Nat) :
    (simCircuit m p n).length ≤ (simulationPolynomial m p).eval n :=
  simCircuit_polynomial_size m p n
#print axioms simCircuit_WF
#print axioms simCircuit_polynomial_size

-- Input-dependent output rules out an answer-table/constant circuit.
def readBit : Machine := ⟨[[.halt false, .halt false, .halt true]]⟩
#eval if output [false] (simCircuit readBit ⟨1, 0⟩ 1) == false then pure () else throw (IO.userError "simulation regression")
#eval if output [true] (simCircuit readBit ⟨1, 0⟩ 1) == true then pure () else throw (IO.userError "simulation regression")

def readSecond : Machine :=
  ⟨[[.move 1 .blank .right, .move 1 .blank .right,
     .move 1 .blank .right, .move 1 .blank .right],
    [.halt false, .halt false, .halt true, .halt false]]⟩
#eval if output [false, true] (simCircuit readSecond ⟨2, 0⟩ 2) == true then pure () else throw (IO.userError "simulation regression")
#eval if output [true, false] (simCircuit readSecond ⟨2, 0⟩ 2) == false then pure () else throw (IO.userError "simulation regression")
#eval if output [true] (simCircuit readSecond ⟨2, 0⟩ 1) == false then pure () else throw (IO.userError "simulation regression")

def acceptAll : Machine := ⟨[[.halt true, .halt true, .halt true, .halt true]]⟩
#eval if output [false] (simCircuit acceptAll ⟨3, 0⟩ 1) == true then pure () else throw (IO.userError "simulation regression")
#eval if output [true] (simCircuit ⟨[]⟩ ⟨3, 0⟩ 1) == false then pure () else throw (IO.userError "simulation regression")
#eval if output [true] (simCircuit acceptAll ⟨0, 0⟩ 1) == false then pure () else throw (IO.userError "simulation regression")

-- Two clocks write a separator, return left, and read it on the third.
def writeSeparator : Machine :=
  ⟨[[.move 1 .separator .right, .move 1 .separator .right,
     .move 1 .separator .right, .move 1 .separator .right],
    [.move 2 .blank .left, .move 2 .blank .left,
     .move 2 .blank .left, .move 2 .blank .left],
    [.halt false, .halt false, .halt false, .halt true]]⟩
#eval if output [false] (simCircuit writeSeparator ⟨3, 0⟩ 1) == true then pure () else throw (IO.userError "simulation regression")

def badState : Machine :=
  ⟨[[.move 99 .blank .stay, .move 99 .blank .stay,
     .move 99 .blank .stay, .move 99 .blank .stay]]⟩
#eval if output [true] (simCircuit badState ⟨2, 0⟩ 1) == false then pure () else throw (IO.userError "simulation regression")

-- A constant circuit cannot simulate both one-bit runs of readBit.
example (C : Circuit) (b : Bool) (hc : ∀ x : Word, x.length = 1 → output x C = b) :
    ¬ (∀ x t a, x.length = 1 → Run readBit (initial x) t a → output x C = a) := by
  intro hs
  have hf := hs [false] 1 false rfl (Run.halt rfl)
  have ht := hs [true] 1 true rfl (Run.halt rfl)
  rw [hc [false] rfl] at hf
  rw [hc [true] rfl] at ht
  cases hf.symm.trans ht
