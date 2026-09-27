module proofs.p_vs_np_undecidable.agda.PvsNPUndecidable where

open import proofs.complexity.agda.Complexity hiding (pSubsetNP)
open import proofs.p_vs_np_decidable.agda.PvsNPDecidable using (_⊎_; excludedMiddle)

-- Syntax is separate from the propositions that statements denote.
data Statement : Set where
  pEqualsNP : Statement
  neg : Statement → Statement

denotes : Statement → Set
denotes pEqualsNP = PEqualsNP
denotes (neg statement) = denotes statement → Empty

-- A formal proof relation must be supplied before this schema refers to ZFC.
record Theory : Set₁ where
  field proves : Statement → Set

Provable : Theory → Statement → Set
Provable theory statement = Theory.proves theory statement

Independent : Theory → Statement → Set
Independent theory statement =
  (Provable theory statement → Empty) ×
  (Provable theory (neg statement) → Empty)

PvsNPIsIndependent : Theory → Set
PvsNPIsIndependent theory = Independent theory pEqualsNP

independence-has-no-proof : (theory : Theory) → PvsNPIsIndependent theory →
  (Provable theory pEqualsNP → Empty) ×
  (Provable theory (neg pEqualsNP) → Empty)
independence-has-no-proof theory h = h

pSubsetNP : (L : Language) → InP L → InNP L
pSubsetNP = proofs.complexity.agda.Complexity.pSubsetNP

pvsnpExcludedMiddle : PEqualsNP ⊎ PNotEqualsNP
pvsnpExcludedMiddle = excludedMiddle PEqualsNP
