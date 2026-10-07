import proofs.experiments.issue624.lean.FixedWindow

open Complexity Issue532.Machines Issue568.Tableau
open Issue624.CertificateCNF Issue624.VerifierTableau Issue624.FixedWindow

example (np : ClassNP) (x : Word) :
    (∃ a trace, WindowVerifierTableau np x a trace) ↔ np.language x = true :=
  windowVerifierTableau_iff_language np x

example (c : Config) (margin width : Nat) (h : span c + 2 * margin ≤ width) :
    span (fitWindow c margin width) = width := fitWindow_span c margin width h

example : span (fitWindow (initial []) 2 7) = 7 := by decide
example : (fitWindow (initial []) 2 7).left.length = 2 := by decide
example : (fitWindow (initial []) 2 7).right.length = 4 := by decide

-- Left padding must preserve the genuine two-way tape semantics, even when
-- the original tape starts with no explicitly represented left cells.
example (c : Config) (q : Nat) (w : Symbol) (k : Nat) :
    TapeEquivalent (moveHead c q w .left)
      (moveHead (fitWindow c k (span c + 2 * k)) q w .left) :=
  tapeEquivalent_moveHead (fitWindow_equivalent c k _) q w .left

example (m : Machine) (c : Config) (t : Nat) (b : Bool) (k width : Nat) :
    Run m (fitWindow c k width) t b ↔ Run m c t b :=
  run_fitWindow_iff m c t b k width

example (m : Machine) (trace : List Config) (c : Config)
    (h : LocalTrace m true trace) (hc : c ∈ trace) : c.state < m.program.length :=
  accepting_trace_state_lt m trace h c hc

example : ¬ LocalTrace moveThenAccept true
    [fitWindow (initial []) 2 7, fitWindow wrongSuccessor 2 7] := by
  simp [LocalTrace, moveThenAccept, wrongSuccessor, fitWindow, step,
    Machine.instruction, initial, initialSymbols, Symbol.index, moveHead, blanks, span]

#print axioms windowVerifierTableau_iff_language
#print axioms run_fitWindow_iff
#print axioms trace_window_of_run

#print axioms windowWidth_polynomial
