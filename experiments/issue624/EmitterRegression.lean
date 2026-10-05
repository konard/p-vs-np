import proofs.experiments.issue624.lean.ConstantEmitter
open Complexity Issue532.Machines Issue624.ConstantEmitter

example (w : Word) : Computes (emitter w) (fun _ => w) (emitterPolynomial w) :=
  emitter_computes w

example : Computes (emitter (encodeCNF [[]])) (fun _ => encodeCNF [[]])
    (emitterPolynomial (encodeCNF [[]])) := emitter_computes _
example : Computes (emitter []) (fun _ => []) (emitterPolynomial []) := emitter_computes _

-- Empty input/output, both bit values, and a long input with a shorter output.
example : (emitter []).program.length = 4 := by decide
example : (emitter [true, false]).program.length = 8 := by decide
private def probe (m : Machine) : Nat → Config → Option Config
  | 0, _ => none
  | fuel + 1, c => if c.state = m.program.length then some c else
    match step m c with
    | .inl _ => none
    | .inr d => probe m fuel d

private def probeWord (w x : Word) : Option (List Symbol × List Symbol) :=
  (probe (emitter w) ((emitterPolynomial w).eval x.length + 1) (initial x)).map
    (fun c => (c.left, c.head :: c.right))

example : probeWord [] [] = some ([], blanks 2) := by decide
example : probeWord [true] [] = some ([], [.one, .blank]) := by decide
example : probeWord [false, true] [true, false, true] =
    some ([], [.zero, .one, .blank, .blank]) := by decide
example : probeWord [true, false, true] [false] =
    some ([], [.one, .zero, .one, .blank]) := by decide

#print axioms emitter_computes
