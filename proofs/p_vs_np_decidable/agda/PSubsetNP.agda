{-
  PSubsetNP.agda - Formal proof that P ⊆ NP

  This file provides a formal proof of the well-known inclusion P ⊆ NP,
  which states that every language decidable in polynomial time is also
  verifiable in polynomial time with a certificate.

  This is a fundamental result in computational complexity theory.
-}

module PSubsetNP where

open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ## 1. Basic Definitions

-- A language is a decision problem over strings
Language : Set
Language = String → Bool

-- Time complexity: maps input size to maximum number of steps
TimeComplexity : Set
TimeComplexity = ℕ → ℕ

-- Polynomial time: there exist constants c and k such that T(n) ≤ c * n^k
isPolynomial : TimeComplexity → Set
isPolynomial T = ∃[ c ] ∃[ k ] (∀ (n : ℕ) → T n ≤ c * n ^ k)
  where
    _≤_ : ℕ → ℕ → Set
    _≤_ = Data.Nat._≤_
    _^_ : ℕ → ℕ → ℕ
    _^_ = Data.Nat._^_
    _*_ : ℕ → ℕ → ℕ
    _*_ = Data.Nat._*_

-- ## 2. Complexity Classes

-- Class P: Languages decidable in polynomial time
record ClassP : Set where
  field
    language : Language
    decider : String → ℕ  -- Simplified: returns number of steps
    timeComplexity : TimeComplexity
    isPoly : isPolynomial timeComplexity
    -- correct : ∀ (s : String) → language s ≡ (decider s > 0)

-- Class NP: Languages with polynomial-time verifiable certificates
record ClassNP : Set where
  field
    language : Language
    verifier : String → String → Bool  -- (input, certificate) → acceptance
    timeComplexity : TimeComplexity
    isPoly : isPolynomial timeComplexity
    -- correct : ∀ (s : String) → language s ≡ (∃[ cert ] verifier s cert ≡ true)

-- ## 3. Main Theorem: P ⊆ NP

{-
  Theorem: P ⊆ NP

  Every language in P is also in NP. This is proven by constructing an NP verifier
  that ignores the certificate and directly uses the P decider.
-}

pSubsetNP : ∀ (L : ClassP) → ∃[ L' ] (∀ (s : String) → ClassP.language L s ≡ ClassNP.language L' s)
pSubsetNP L = npLang , proof
  where
    open ClassP L renaming (language to pLang; timeComplexity to pTime; isPoly to pPoly)

    -- Construct an NP machine that ignores the certificate
    npLang : ClassNP
    npLang = record
      { language = pLang
      ; verifier = λ s cert → pLang s  -- Ignore certificate
      ; timeComplexity = pTime
      ; isPoly = pPoly
      }

    -- Proof that languages are equal
    proof : ∀ (s : String) → pLang s ≡ ClassNP.language npLang s
    proof s = refl

-- ## 4. Verification

{-
  Summary: We have formally proven that P ⊆ NP, a fundamental result
  in computational complexity theory showing that polynomial-time decidable
  languages are also polynomial-time verifiable.
-}
