import proofs.experiments.issue624.lean.Schema
import proofs.experiments.issue624.lean.CookLevin

open Complexity Issue532.Machines Issue624.Schema Issue624.CookLevin
open Issue624.VerifierTableau

-- The finite description depends only on the fixed verifier witness.
example : ClassNP → Schema := tableauSchema

-- The emitter's input must describe the exact existing formula, on all inputs.
example (np : ClassNP) (x : Word) :
    evalSchema (tableauSchema np) (tableauParams np x.length) x (fun _ => 0) =
      tableauCNF np x := tableauSchema_eq np x

-- Also check the non-definitional equation with the original CNF fragments.
example (np : ClassNP) (x : Word) (env : Nat → Nat) :
    evalSchema (tableauSchema np) (tableauParams np x.length) x env =
      Issue624.CertificateCNF.certificateCNF 0 (np.certBound.eval x.length) ++
        Issue624.InitialCNF.initialCNF (rowBase np x)
          (verifierMachine np.verifier).program.length (Issue624.VerifierTableau.maxClock np x.length)
          (sources np x) ++
        Issue624.RunCNF.runCNF (verifierMachine np.verifier) (rowBase np x)
          (Issue624.FixedWindow.windowWidth np x.length) (Issue624.VerifierTableau.maxClock np x.length) :=
  tableauSchema_fragments np x env

-- Finite expression probes: truncated subtraction, missing reads, and bits.
example : evalExpr (.sub (.const 2) (.const 5)) [] [] (fun _ => 0) = 0 := rfl
example : evalExpr (.bit (.const 1)) [] [false, true] (fun _ => 0) = 1 := rfl
example : evalExpr (.bit (.const 3)) [] [true] (fun _ => 0) = 0 := rfl
example : evalExpr (.param 3) [7] [] (fun _ => 0) = 0 := rfl

-- One-hot output contains the long positive clause and every negative pair.
example : evalSchema (oneHotSchema 0 (.const 4) (.const 3)) [] [] (fun _ => 0) =
    [[⟨4, true⟩, ⟨5, true⟩, ⟨6, true⟩],
     [⟨4, false⟩, ⟨5, false⟩], [⟨4, false⟩, ⟨6, false⟩],
     [⟨5, false⟩, ⟨6, false⟩]] := by decide

example : evalSchema (certificateSchema 0 (.const 0) (.const 0)) [] [] (fun _ => 0) =
    [[⟨0, false⟩]] := rfl

-- Nested loops retain the outer slot while their bounds depend on it.
example : evalSchema (.forRange 0 (.const 2)
    (.forRange 1 (.add (.idx 0) (.const 1))
      (.clause (.list [(.add (.mul (.const 10) (.idx 0)) (.idx 1), true)]))))
      [] [] (fun _ => 99) = [[⟨0, true⟩], [⟨10, true⟩], [⟨11, true⟩]] := by decide
