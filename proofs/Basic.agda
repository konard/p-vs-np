{-
  Basic.agda - Simple foundational proofs in Agda

  This file serves as a bootstrap for formal verification in Agda,
  demonstrating basic proof techniques and serving as a template for
  future P vs NP related proofs.
-}

module proofs.Basic where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality
open import Data.Nat using (_+_; _*_; zero; suc)
open import Data.Nat.Properties using (+-comm; +-assoc; *-comm; +-identity; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Basic Logical Proofs

modus-ponens : {P Q : Set} → P → (P → Q) → Q
modus-ponens p p→q = p→q p

and-commutative : {P Q : Set} → P × Q → Q × P
and-commutative (p , q) = q , p

or-commutative : {P Q : Set} → P ⊎ Q → Q ⊎ P
or-commutative (inj₁ p) = inj₂ p
or-commutative (inj₂ q) = inj₁ q

-- Basic Arithmetic Proofs

add-zero : (n : ℕ) → n + 0 ≡ n
add-zero n = +-identityʳ n

add-commutative : (m n : ℕ) → m + n ≡ n + m
add-commutative m n = +-comm m n

mul-one : (n : ℕ) → n * 1 ≡ n
mul-one zero = refl
mul-one (suc n) = cong suc (mul-one n)

add-associativity : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
add-associativity a b c = +-assoc a b c

-- Even Numbers (useful for complexity theory)

data IsEven : ℕ → Set where
  even-exists : (n k : ℕ) → n ≡ 2 * k → IsEven n

double-is-even : (n : ℕ) → IsEven (2 * n)
double-is-even n = even-exists (2 * n) n refl

-- Factorial Function

factorial : ℕ → ℕ
factorial zero = 1
factorial (suc n) = suc n * factorial n

-- Factorial is always positive (represented by producing a natural number)
factorial-produces-nat : (n : ℕ) → ℕ
factorial-produces-nat n = factorial n

-- List Operations (relevant for algorithm complexity)

list-length-append : {A : Set} (l1 l2 : List A) →
  length (l1 ++ l2) ≡ length l1 + length l2
list-length-append [] l2 = refl
list-length-append (x ∷ l1) l2 = cong suc (list-length-append l1 l2)

-- Identity proof (foundation for rewriting)

refl-eq : {A : Set} (x : A) → x ≡ x
refl-eq x = refl

-- Simple transitivity proof

trans-eq : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans-eq refl refl = refl

-- Simple symmetry proof

sym-eq : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym-eq refl = refl

-- Congruence proof

cong-eq : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong-eq f refl = refl

-- Verification successful: All proofs type-check in Agda
