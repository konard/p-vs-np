import proofs.experiments.issue624.lean.CircuitCNF

open Complexity Issue532.Machines Issue532.Circuits Issue624.CircuitCNF

-- The compiler must reuse the existing NAND circuit semantics.
example (n : Nat) (C : Circuit) (hw : WF n C) :
    Satisfiable (acceptingCNF n C) ↔ ∃ x : Word, x.length = n ∧ output x C = true :=
  acceptingCNF_iff n C hw

-- No input wire exists at length zero, so the empty circuit outputs false.
example : ¬ Satisfiable (acceptingCNF 0 []) := by
  rw [acceptingCNF_iff 0 [] (by trivial)]
  simp [output, wires]

-- NAND(x,x) has a model, whereas NAND followed by x AND NOT x does not.
example : Satisfiable (acceptingCNF 1 [(0, 0)]) :=
  (acceptingCNF_iff 1 [(0, 0)] (by simp [WF, WFfrom])).mpr
    ⟨[false], rfl, rfl⟩
example : ¬ Satisfiable (acceptingCNF 1 [(0, 0), (0, 1), (2, 2)]) := by
  rw [acceptingCNF_iff 1 _ (by simp [WF, WFfrom])]
  rintro ⟨x, hx, ho⟩
  cases x with
  | nil => simp at hx
  | cons b tail =>
    have ht : tail = [] := by simpa using hx
    subst tail
    cases b <;> cases ho

-- Incorrect gate outputs are rejected assignment by assignment.
example : evalCNF (fun _ => true) (gateCNF 2 0 1) = false := by decide
example : evalCNF (fun _ => false) (gateCNF 2 0 1) = false := by decide
example (a : Assignment) : evalCNF a (gateCNF 2 0 1) = true ↔
    a 2 = !(a 0 && a 1) := gateCNF_models a 2 0 1

example (n : Nat) (C : Circuit) (hw : WF n C) :
    (encodeCNF (acceptingCNF n C)).length ≤
      8 * (3 * C.length + 1) * (n + C.length + 1) :=
  acceptingCNF_encoded_size n C hw

#print axioms acceptingCNF_iff
#print axioms circuitCNF_models
#print axioms acceptingCNF_encoded_size

example (p : Polynomial) (inputLength n : Nat) (C : Circuit)
    (hw : WF n C) (hs : n + C.length ≤ p.eval inputLength) :
    (encodeCNF (acceptingCNF n C)).length ≤
      (circuitPolynomial p).eval inputLength :=
  acceptingCNF_polynomial_size p inputLength n C hw hs

#print axioms acceptingCNF_polynomial_size
