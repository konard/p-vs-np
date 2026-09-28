module experiments.issue572.Independent where

open import proofs.complexity.agda.Complexity using (Empty; PNotEqualsNP; pair; snd)
open import proofs.p_vs_np_undecidable.agda.PvsNPUndecidable
open import Agda.Builtin.Equality using (_≡_; refl)

emptyTheory : Theory
emptyTheory = record { proves = λ _ → Empty }

empty-theory-independent : PvsNPIsIndependent emptyTheory
empty-theory-independent = pair (λ h → h) (λ h → h)

negation-denotes-p-not-equals-np : denotes (neg pEqualsNP) ≡ PNotEqualsNP
negation-denotes-p-not-equals-np = refl

independent-cannot-prove-negation : (theory : Theory) →
  PvsNPIsIndependent theory → Provable theory (neg pEqualsNP) → Empty
independent-cannot-prove-negation theory h = snd h
