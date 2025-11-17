import proofs.basic.lean.Basic
import proofs.p_not_equal_np.lean.PNotEqualNP
import proofs.p_eq_np.lean.PvsNP
import proofs.p_vs_np_undecidable.lean.PvsNPUndecidable
import proofs.p_vs_np_decidable.lean.PSubsetNP
-- Import Tang Pushan attempt formalization (hyphens not allowed in Lean paths)
-- Note: The directory name uses hyphens but Lean import uses underscores

def main : IO Unit :=
  IO.println "P vs NP Project - Lean Verification"
