module proofs.p_vs_np_decidable.agda.PSubsetNP where

open import proofs.complexity.agda.Complexity hiding (pSubsetNP)

-- A P machine is an NP verifier that ignores the empty certificate.
pSubsetNP : (L : Language) → InP L → InNP L
pSubsetNP = proofs.complexity.agda.Complexity.pSubsetNP
