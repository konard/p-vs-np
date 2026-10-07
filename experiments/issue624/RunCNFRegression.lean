import proofs.experiments.issue624.lean.RunCNF

open Complexity Issue532.Machines Issue568.Tableau Issue624.RunCNF

set_option maxRecDepth 2048

private def accept : Machine := ⟨[[.halt true, .halt true, .halt true, .halt true]]⟩
private def reject : Machine := ⟨[[.halt false, .halt false, .halt false, .halt false]]⟩
private def startSensitive : Machine :=
  ⟨[[.halt false, .halt false, .halt false, .halt false],
    [.halt true, .halt true, .halt true, .halt true]]⟩
private def first : Config := ⟨0, [.blank], .blank, [.blank]⟩
private def last : Config := ⟨1, [.blank], .blank, [.blank]⟩
private def wrong : Config := ⟨1, [.blank], .one, [.blank]⟩
private def model (m : Machine) (trace : List Config) : Assignment :=
  traceAssignment 7 m.program.length 3 trace

example : evalCNF (model accept [first]) (runCNF accept 7 3 1) = true := by decide
-- Unused suffix rows require no arbitrary state/head/tape selections.
example : evalCNF (model accept [first]) (runCNF accept 7 3 3) = true := by decide
example : evalCNF (fun v => if v < nextBase 7 1 3 then model accept [first] v else true)
    (runCNF accept 7 3 3) = true := by decide
example : evalCNF (model accept [first]) (runCNF accept 7 3 0) = false := by decide
example : evalCNF (model reject [first]) (runCNF reject 7 3 3) = false := by decide
-- Initial-row wiring is essential: rejection from state zero does not
-- exclude an accepting trace beginning at an unrelated state.
example : step startSensitive (initial []) = .inl false := by rfl
example : evalCNF (model startSensitive [first]) (runCNF startSensitive 7 3 1) = false := by decide
example : evalCNF (model startSensitive [last]) (runCNF startSensitive 7 3 1) = true := by decide
example : evalCNF (model accept [first, first]) (runCNF accept 7 3 3) = false := by decide
example : evalCNF (model moveThenAccept [first, last]) (runCNF moveThenAccept 7 3 2) = true := by decide
example : evalCNF (model moveThenAccept [first, last]) (runCNF moveThenAccept 7 3 1) = false := by decide
example : evalCNF (model moveThenAccept [first]) (runCNF moveThenAccept 7 3 2) = false := by decide
example : evalCNF (model moveThenAccept [first, wrong]) (runCNF moveThenAccept 7 3 2) = false := by decide
example : decodeTrace moveThenAccept 7 3 2 (model moveThenAccept [first, last]) = [first, last] := by rfl
example : evalCNF (fun _ => false) (runCNF accept 7 3 1) = false := by decide
example : evalCNF (fun _ => true) (runCNF accept 7 3 1) = false := by decide
example : evalCNF (fun _ => true) (runCNF ⟨[]⟩ 7 3 1) = false := by decide
example : evalCNF (fun _ => true) (runCNF accept 7 0 1) = false := by decide
example : ¬Satisfiable (runCNF reject 7 3 3) :=
  runCNF_rejecting_unsatisfiable reject 7 3 3 (by
    intro ⟨q, l, s, r⟩; cases q <;> cases s <;> rfl)
example : (encodeCNF (runCNF moveThenAccept 7 3 2)).length ≤ runSize moveThenAccept 7 3 2 :=
  runCNF_encoded_size _ _ _ _
example : (encodeCNF (runCNF moveThenAccept 7 3 2)).length ≤
    (runPolynomial moveThenAccept ⟨7, 0⟩ ⟨3, 0⟩ ⟨2, 0⟩).eval 0 :=
  runCNF_polynomial_size _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)

#print axioms runCNF_sound
#print axioms runCNF_complete
#print axioms runCNF_models
#print axioms runCNF_wrong_successor_rejected
#print axioms runCNF_encoded_size
#print axioms runCNF_polynomial_size
#print axioms runCNF_rejecting_unsatisfiable
