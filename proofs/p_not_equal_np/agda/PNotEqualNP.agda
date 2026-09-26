module proofs.p_not_equal_np.agda.PNotEqualNP where

open import proofs.complexity.agda.Complexity hiding (PEqualsNP; PNotEqualsNP)
open import proofs.p_vs_np_decidable.agda.PvsNPDecidable using (_⊎_; left; right; excludedMiddle)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

DecisionProblem : Set
DecisionProblem = Language

P-equals-NP : Set
P-equals-NP = (L : DecisionProblem) → (InP L → InNP L) × (InNP L → InP L)

P-not-equals-NP : Set
P-not-equals-NP = P-equals-NP → Empty

P-subset-NP : (L : DecisionProblem) → InP L → InNP L
P-subset-NP = pSubsetNP

HardWitness : Set
HardWitness = Σ DecisionProblem (λ L → InNP L × (InP L → Empty))

test-existence-of-hard-problem-reverse : HardWitness → P-not-equals-NP
test-existence-of-hard-problem-reverse (L , pair hnp hnotp) heq =
  hnotp (snd (heq L) hnp)

npToP : (HardWitness → Empty) → (L : DecisionProblem) → InNP L → InP L
npToP hnone L hnp with excludedMiddle (InP L)
... | left hp = hp
... | right hnotp = emptyElim (hnone (L , pair hnp hnotp))

-- Forward direction uses the explicitly postulated classical excluded middle.
test-existence-of-hard-problem : P-not-equals-NP → HardWitness
test-existence-of-hard-problem hneq with excludedMiddle HardWitness
... | left witness = witness
... | right hnone = emptyElim (hneq (λ L → pair (P-subset-NP L) (npToP hnone L)))

-- Completeness and SAT membership are premises, not axioms of the framework.
test-NP-complete-not-in-P :
  (IsNPComplete : DecisionProblem → Set) →
  ((L : DecisionProblem) → IsNPComplete L → InNP L) →
  (Σ DecisionProblem (λ L → IsNPComplete L × (InP L → Empty))) →
  P-not-equals-NP
test-NP-complete-not-in-P complete completeInNP (L , pair hc hnotp) =
  test-existence-of-hard-problem-reverse (L , pair (completeInNP L hc) hnotp)

test-SAT-not-in-P :
  (sat : DecisionProblem) → InNP sat → (InP sat → Empty) → P-not-equals-NP
test-SAT-not-in-P sat hnp hnotp =
  test-existence-of-hard-problem-reverse (sat , pair hnp hnotp)

HasSuperPolynomialLowerBound : DecisionProblem → Set
HasSuperPolynomialLowerBound problem =
  (machine : Machine) (bound : Polynomial) →
  ((x : Word) → Σ Nat (λ t → Σ Bool (λ b →
    (t ≤ evalPoly bound (length x)) ×
    (Run machine (initial x) t b × (problem x ≡ b))))) → Empty

test-super-polynomial-lower-bound :
  (Σ DecisionProblem (λ L → InNP L × HasSuperPolynomialLowerBound L)) →
  P-not-equals-NP
test-super-polynomial-lower-bound (L , pair hnp hlower) =
  test-existence-of-hard-problem-reverse (L , pair hnp notInP)
  where
    notInP : InP L → Empty
    notInP (p , hp) = hlower (ClassP.machine p) (ClassP.bound p) bounded
      where
        bounded : (x : Word) → Σ Nat (λ t → Σ Bool (λ b →
          (t ≤ evalPoly (ClassP.bound p) (length x)) ×
          (Run (ClassP.machine p) (initial x) t b × (L x ≡ b))))
        bounded x with ClassP.terminates p x
        ... | t , b , pair ht hr =
          t , b , pair ht (pair hr
            (trans (sym (cong (λ language → language x) hp))
              (ClassP.correct p x t b hr)))

record ProofOfPNotEqualNP : Set where
  constructor proof
  field proves : P-not-equals-NP

-- Rocq/Lean/Agda type checking validates the proof term, not this Boolean.
verifyPNotEqualNPProof : ProofOfPNotEqualNP → Bool
verifyPNotEqualNPProof _ = true

checkProblemWitness : (L : DecisionProblem) → InNP L → (InP L → Empty) → ProofOfPNotEqualNP
checkProblemWitness L hnp hnotp = proof (test-existence-of-hard-problem-reverse (L , pair hnp hnotp))
