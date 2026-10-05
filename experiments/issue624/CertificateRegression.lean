import proofs.experiments.issue624.lean.CertificateCNF
import proofs.experiments.issue624.lean.VerifierTableau

open Complexity Issue532.Machines Issue624.CertificateCNF
open Issue624.VerifierTableau

#check certificateCNF_models
#check decodeCertificate_length
#check encodeCertificate_models
#check decode_encodeCertificate
#check encode_certificateCNF_length
#check certificateCNF_polynomial_size
#check certificateCNF_variables
#check Issue624.VerifierTableau.verifierTableau_iff_language
#check Issue624.VerifierTableau.verifierTableau_span

-- Empty and short certificates, including both possible values, are distinct.
example : decodeCertificate (encodeCertificate []) 0 3 = [] := by decide
example : decodeCertificate (encodeCertificate [false]) 0 3 = [false] := by decide
example : decodeCertificate (encodeCertificate [true, false]) 0 3 = [true, false] := by decide
example : (encodeCNF (certificateCNF 0 0)).length = 4 := by decide
example : (encodeCNF (certificateCNF 0 1)).length = 26 := by decide
example : (encodeCNF (certificateCNF 0 2)).length = 64 := by decide
example : (encodeCNF (certificateCNF 2 3)).length = 222 := by
  rw [encode_certificateCNF_length]

-- A bit after a blank, a noncanonical blank, and the sentinel are rejected.
example : evalCNF (fun v => decide (v = 2)) (certificateCNF 0 2) = false := by decide
example : evalCNF (fun v => decide (v = 1)) (certificateCNF 0 1) = false := by decide
example : evalCNF (encodeCertificate [true, false]) (certificateCNF 0 1) = false := by decide

private def constantMachine (answer : Bool) : Machine :=
  ⟨[[.halt answer, .halt answer, .halt answer, .halt answer]]⟩

private theorem constantRun (answer : Bool) (c : Config) (h : c.state = 0) :
    Run (constantMachine answer) c 1 answer := by
  apply Run.halt
  unfold step
  rw [h]
  cases c.head <;> rfl

private def constantVerifier (paired : Bool) (answer : Bool) : VerifierProgram :=
  if paired then .paired (constantMachine answer) else .ignoreCertificate (constantMachine answer)

private theorem constantVerifierRun (paired answer : Bool) (x cert : Word) :
    (constantVerifier paired answer).Run x cert 1 answer := by
  cases paired <;> change Run (constantMachine answer) _ 1 answer <;>
    apply constantRun <;> cases x <;> rfl

private theorem constantTime (paired answer : Bool) (x cert : Word) :
    (constantVerifier paired answer).timeLimit ⟨1, 0⟩ x cert = 1 := by
  cases paired <;> rfl

/-- Concrete NP witnesses exercise both constructors without assuming NP membership. -/
private def constantNP (paired answer : Bool) (bound : Nat) : ClassNP where
  language := fun _ => answer
  verifier := constantVerifier paired answer
  timeBound := ⟨1, 0⟩
  certBound := ⟨bound, 0⟩
  terminates := fun x cert _ =>
    ⟨1, answer, by rw [constantTime]; exact Nat.le_refl 1,
      constantVerifierRun paired answer x cert⟩
  correct := by
    intro x
    constructor
    · intro h
      exact ⟨[], 1, by simp, by rw [constantTime]; exact Nat.le_refl 1,
        h ▸ constantVerifierRun paired answer x []⟩
    · rintro ⟨cert, t, _, _, hr⟩
      exact ((run_deterministic ((verifierRun_iff _ _ _ _ _).mp hr)
        ((verifierRun_iff _ _ _ _ _).mp (constantVerifierRun paired answer x cert))).2).symm

example : VerifierTableau (constantNP true true 3) [] (encodeCertificate [])
    [pairedInput [] []] := by
  exact ⟨by decide, rfl, by decide, rfl⟩
example : VerifierTableau (constantNP true true 3) [] (encodeCertificate [false])
    [pairedInput [] [false]] := by
  exact ⟨by decide, rfl, by decide, rfl⟩
example : VerifierTableau (constantNP false true 3) [true] (encodeCertificate [false])
    [initial [true]] := by
  exact ⟨by decide, rfl, by decide, rfl⟩
example (x : Word) : ¬ ∃ a trace, VerifierTableau (constantNP true false 3) x a trace :=
  rejecting_verifier_no_tableau _ x rfl
example (x : Word) : ¬ ∃ a trace, VerifierTableau (constantNP false false 3) x a trace :=
  rejecting_verifier_no_tableau _ x rfl

-- Clock and input construction depend on the decoded length, not the capacity.
example : (VerifierProgram.paired (constantMachine true)).timeLimit ⟨1, 1⟩ []
    (decodeCertificate (encodeCertificate []) 0 3) = 2 := by decide
example : (VerifierProgram.paired (constantMachine true)).timeLimit ⟨1, 1⟩ []
    (decodeCertificate (encodeCertificate [false]) 0 3) = 3 := by decide
example : ¬ Represents (encodeCertificate [true, false]) 0 [true, false] 1 :=
  overlong_not_representable _ _ _ (by decide)

example : ¬ Issue568.Tableau.LocalTrace Issue568.Tableau.moveThenAccept true
    [initial [], Issue568.Tableau.wrongSuccessor] := Issue568.Tableau.wrong_successor_rejected

#print axioms certificateCNF_models
#print axioms encodeCertificate_models
#print axioms decode_encodeCertificate
#print axioms certificateCNF_polynomial_size
#print axioms encode_certificateCNF_length
#print axioms certificateCNF_variables
#print axioms overlong_rejected
#print axioms Issue624.VerifierTableau.verifierTableau_iff_language
#print axioms Issue624.VerifierTableau.maxClock_polynomial
#print axioms Issue624.VerifierTableau.verifierTableau_span
#print axioms Issue624.VerifierTableau.wrong_successor_not_model
