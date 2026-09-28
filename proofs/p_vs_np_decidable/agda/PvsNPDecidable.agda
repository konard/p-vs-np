module proofs.p_vs_np_decidable.agda.PvsNPDecidable where

open import proofs.complexity.agda.Complexity hiding (pSubsetNP; PEqualsNP; PNotEqualsNP)
open import Agda.Builtin.Equality using (_≡_; refl)

data _⊎_ (A B : Set) : Set where
  left : A → A ⊎ B
  right : B → A ⊎ B

-- Classical excluded middle is explicit. It supplies no decision algorithm.
postulate
  excludedMiddle : (P : Set) → P ⊎ (P → Empty)

PEqualsNP : Set
PEqualsNP = proofs.complexity.agda.Complexity.PEqualsNP

PNotEqualsNP : Set
PNotEqualsNP = PEqualsNP → Empty

is-decidable : Set → Set
is-decidable P = P ⊎ (P → Empty)

P-vs-NP-is-decidable : PEqualsNP ⊎ PNotEqualsNP
P-vs-NP-is-decidable = excludedMiddle PEqualsNP

P-vs-NP-decidable : is-decidable PEqualsNP
P-vs-NP-decidable = excludedMiddle PEqualsNP

P-vs-NP-has-answer : PEqualsNP ⊎ PNotEqualsNP
P-vs-NP-has-answer = excludedMiddle PEqualsNP

pSubsetNP : (L : Language) → InP L → InNP L
pSubsetNP = proofs.complexity.agda.Complexity.pSubsetNP

pvsnpIsWellFormed : Set
pvsnpIsWellFormed = PEqualsNP ⊎ PNotEqualsNP

decidability-reflexive : (P : Set) → is-decidable P ≡ (P ⊎ (P → Empty))
decidability-reflexive P = refl

decidability-implies-answer : is-decidable PEqualsNP → PEqualsNP ⊎ PNotEqualsNP
decidability-implies-answer h = h
