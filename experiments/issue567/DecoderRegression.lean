import proofs.experiments.issue532.lean.Idea41

open Issue532.Idea41

-- These checks fail to elaborate until the shared encoding has an executable
-- Lean decoder. They also exercise malformed and trailing input.
example : decCircuit (encCircuit 1 [(0, 0)]) = some (1, [(0, 0)]) := by decide
example : decCircuit (encCircuit 1 [(0, 0)] ++ [true]) = none := by decide
example : decCircuit [true] = none := by decide
example : checkCircuit (encCircuit 1 [(0, 1)]) = false := by decide
example : checkCircuit (encCircuit 0 [(0, 0)]) = false := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)]) [false] = true := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)]) [true] = false := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)]) [] = false := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)] ++ [true]) [false] = false := by decide
example : verifyCircuit (encCircuit 0 []) [] = false := by decide
example : verifyCircuit (encCircuit 1 []) [true] = true := by decide
