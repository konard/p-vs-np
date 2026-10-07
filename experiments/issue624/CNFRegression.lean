import proofs.experiments.issue624.lean.LocalCNF
open Complexity Issue532.Machines Issue624.LocalCNF

example : evalCNF (fun _ => false) (oneHot 7 0) = false := by decide
example : evalCNF (fun _ => false) (oneHot 7 3) = false := by decide
example : evalCNF (fun _ => true) (oneHot 7 3) = false := by decide
example : evalCNF (fun i => i == 8) (oneHot 7 3) = true := by decide
example (a : Assignment) (base size : Nat) :
    evalCNF a (oneHot base size) = true ↔
      ∃ v, v < size ∧ a (base + v) = true ∧
        ∀ w, w < size → a (base + w) = true → w = v :=
  oneHot_models a base size

-- A locally accepting final row cannot override a false transition clause.
example : evalClause (fun _ => true) (implies [⟨0, true⟩, ⟨1, true⟩] []) = false := by decide
example : evalClause (fun i => i != 1) (implies [⟨0, true⟩, ⟨1, true⟩] []) = true := by decide
example : evalClause (fun _ => true) (implies [] []) = false := by decide
example : evalClause (fun _ => true) (implies [] [⟨5, true⟩]) = true := by decide

#print axioms oneHot_models
#print axioms implies_models
#print axioms oneHot_encoded_size
