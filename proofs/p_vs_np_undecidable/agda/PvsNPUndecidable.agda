module proofs.p_vs_np_undecidable.agda.PvsNPUndecidable where

open import proofs.complexity.agda.Complexity hiding (pSubsetNP)
open import proofs.p_vs_np_decidable.agda.PvsNPDecidable using (_⊎_; excludedMiddle)

-- A proof relation must be supplied before this schema refers to any theory.
record Theory : Set₁ where
  field proves : Set → Set

Independent : Theory → Set → Set
Independent theory statement =
  (Theory.proves theory statement → Empty) ×
  (Theory.proves theory (statement → Empty) → Empty)

PvsNPIsIndependent : Theory → Set
PvsNPIsIndependent theory = Independent theory PEqualsNP

independence-has-no-proof : (theory : Theory) → PvsNPIsIndependent theory →
  (Theory.proves theory PEqualsNP → Empty) ×
  (Theory.proves theory PNotEqualsNP → Empty)
independence-has-no-proof theory h = h

pSubsetNP : (L : Language) → InP L → InNP L
pSubsetNP = proofs.complexity.agda.Complexity.pSubsetNP

pvsnpExcludedMiddle : PEqualsNP ⊎ PNotEqualsNP
pvsnpExcludedMiddle = excludedMiddle PEqualsNP
