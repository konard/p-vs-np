import proofs.experiments.issue532.lean.Idea37
open Issue532.Idea37

/-- (a) `time` is a free parameter: with the zero cost function, any correct
algorithm meets `LogParamFPTObligation` (parameter `0`, `c = b = 0`). -/
theorem idea37_obligation_of_correct {Inst Alg : Type} (Correct : Alg → Prop)
    (size : Inst → Nat) (A : Alg) (hA : Correct A) :
    LogParamFPTObligation Correct (fun _ _ => 0) size :=
  ⟨A, fun _ => 0, 0, 0, hA, fun _ => Nat.zero_le _, fun _ => by simp⟩

/-- E.g. algorithms = Boolean functions on CNF-like inputs, `Correct A := A = L`. -/
theorem idea37_obligation_trivial {Inst : Type} (L : Inst → Bool) (size : Inst → Nat) :
    LogParamFPTObligation (fun A : Inst → Bool => A = L) (fun _ _ => 0) size :=
  idea37_obligation_of_correct _ size L rfl
