import proofs.experiments.issue567.lean.CircuitSyntax
import proofs.experiments.issue10.lean.NPNotSubsetP

open Complexity Issue532.Idea41 Issue567.CircuitSyntax

example : circuitSyntaxMachine.program.length = 6 := by decide
example : circuitSyntax (encCircuit 2 [(0, 1), (2, 1)]) = true := by decide
example : circuitSyntax (encCircuit 0 []) = true := by decide
example : circuitSyntax [] = false := by decide
example : circuitSyntax [true] = false := by decide
example : circuitSyntax (encCircuit 1 [(0, 0)] ++ [true]) = false := by decide
example : circuitSyntax [true, false, true, false] = false := by decide
example : circuitSyntax [true, false, true, false, true] = false := by decide

-- A real charged run, with both positive and negative answers.
example : Run circuitSyntaxMachine (pairedInput (encCircuit 1 [(0, 0)]) [false])
    ((encCircuit 1 [(0, 0)]).length + 1) true :=
  circuitSyntaxMachine_run _ _
example : Run circuitSyntaxMachine (pairedInput [true] [false]) 2 false :=
  circuitSyntaxMachine_run _ _
example (m : Machine) (x cert : Word) (b : Bool) : ¬ Run m (pairedInput x cert) 0 b := by
  intro hr
  have := Issue10.NPNotSubsetP.run_pos hr
  omega

-- Syntax alone would accept these. The full verifier must reject them.
example : circuitSyntax (encCircuit 1 [(0, 1)]) = true := by decide
example : verifyCircuit (encCircuit 1 [(0, 1)]) [false] = false := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)]) [] = false := by decide
example : verifyCircuit (encCircuit 1 [(0, 0)]) [false, true] = false := by decide
example : verifyCircuit (encCircuit 1 []) [true] = true := by decide
example : verifyCircuit (encCircuit 1 []) [false] = false := by decide

-- Replacing every certificate by [false] also breaks the existential language
-- relation on the smallest circuit whose only satisfying input is [true].
example : ¬ (CircuitSAT (encCircuit 1 []) = true ↔
    ∃ cert : Word, verifyCircuit (encCircuit 1 []) [false] = true) := by
  intro he
  have hs : CircuitSAT (encCircuit 1 []) = true :=
    (circuitSAT_iff_verifyCircuit _).mpr ⟨[true], rfl⟩
  obtain ⟨_, hc⟩ := he.mp hs
  change false = true at hc
  contradiction

-- Any pointwise-correct verifier must distinguish the two certificates.
example (v : Word → Word → Bool)
    (hv : ∀ x cert, v x cert = verifyCircuit x cert)
    (blind : ∀ x a b, v x a = v x b) : False := by
  have he := blind (encCircuit 1 []) [true] [false]
  rw [hv, hv] at he
  change true = false at he
  contradiction
