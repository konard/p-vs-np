module proofs.complexity.agda.Complexity where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data Empty : Set where

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

infixr 4 _×_
data _×_ (A B : Set) : Set where
  pair : A → B → A × B

fst : ∀ {A B} → A × B → A
fst (pair a b) = a
snd : ∀ {A B} → A × B → B
snd (pair a b) = b

Word : Set
Word = List Bool
Language : Set
Language = Word → Bool

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

lookup : ∀ {A : Set} → List A → Nat → Maybe A
lookup [] _ = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc n) = lookup xs n

data Symbol : Set where
  blank zeroBit oneBit separator : Symbol

ofBool : Bool → Symbol
ofBool false = zeroBit
ofBool true = oneBit

symbolIndex : Symbol → Nat
symbolIndex blank = 0
symbolIndex zeroBit = 1
symbolIndex oneBit = 2
symbolIndex separator = 3

data Direction : Set where
  left right stay : Direction

data Instruction : Set where
  halt : Bool → Instruction
  move : Nat → Symbol → Direction → Instruction

record Machine : Set where
  constructor mkMachine
  field program : List (List Instruction)

record Config : Set where
  constructor config
  field
    state : Nat
    tapeLeft : List Symbol
    tapeHead : Symbol
    tapeRight : List Symbol

initialSymbols : List Symbol → Config
initialSymbols [] = config 0 [] blank []
initialSymbols (a ∷ rest) = config 0 [] a rest

initial : Word → Config
initial x = initialSymbols (map ofBool x)

pairedInput : Word → Word → Config
pairedInput x cert = initialSymbols (map ofBool x ++ (separator ∷ []) ++ map ofBool cert)

instruction : Machine → Nat → Symbol → Instruction
instruction m q a with lookup (Machine.program m) q
... | nothing = halt false
... | just row with lookup row (symbolIndex a)
...   | nothing = halt false
...   | just i = i

moveHead : Config → Nat → Symbol → Direction → Config
moveHead c next write stay = config next (Config.tapeLeft c) write (Config.tapeRight c)
moveHead c next write left with Config.tapeLeft c
... | [] = config next [] blank (write ∷ Config.tapeRight c)
... | a ∷ rest = config next rest a (write ∷ Config.tapeRight c)
moveHead c next write right with Config.tapeRight c
... | [] = config next (write ∷ Config.tapeLeft c) blank []
... | a ∷ rest = config next (write ∷ Config.tapeLeft c) a rest

data Result (A B : Set) : Set where
  inl : A → Result A B
  inr : B → Result A B

step : Machine → Config → Result Bool Config
step m c with instruction m (Config.state c) (Config.tapeHead c)
... | halt b = inl b
... | move next write dir = inr (moveHead c next write dir)

data Run (m : Machine) : Config → Nat → Bool → Set where
  runHalt : ∀ {c b} → step m c ≡ inl b → Run m c 1 b
  runNext : ∀ {c c' t b} → step m c ≡ inr c' → Run m c' t b → Run m c (suc t) b

pow : Nat → Nat → Nat
pow n zero = 1
pow n (suc k) = n * pow n k

record Polynomial : Set where
  constructor poly
  field
    coefficient : Nat
    degree : Nat

evalPoly : Polynomial → Nat → Nat
evalPoly p n = Polynomial.coefficient p * pow (suc n) (Polynomial.degree p)

record ClassP : Set where
  field
    language : Language
    machine : Machine
    bound : Polynomial
    terminates : (x : Word) → Σ Nat (λ t → Σ Bool (λ b →
      (t ≤ evalPoly bound (length x)) × Run machine (initial x) t b))
    correct : (x : Word) (t : Nat) (b : Bool) →
      Run machine (initial x) t b → language x ≡ b

data VerifierProgram : Set where
  ignoreCertificate : Machine → VerifierProgram
  paired : Machine → VerifierProgram

verifierRun : VerifierProgram → Word → Word → Nat → Bool → Set
verifierRun (ignoreCertificate m) x cert t b = Run m (initial x) t b
verifierRun (paired m) x cert t b = Run m (pairedInput x cert) t b

timeLimit : VerifierProgram → Polynomial → Word → Word → Nat
timeLimit (ignoreCertificate m) p x cert = evalPoly p (length x)
timeLimit (paired m) p x cert = evalPoly p (length x + length cert + 1)

record ClassNP : Set where
  field
    language : Language
    verifier : VerifierProgram
    timeBound : Polynomial
    certBound : Polynomial
    terminates : (x cert : Word) → length cert ≤ evalPoly certBound (length x) →
      Σ Nat (λ t → Σ Bool (λ b →
        (t ≤ timeLimit verifier timeBound x cert) ×
        verifierRun verifier x cert t b))
    correct : (x : Word) →
      ((language x ≡ true) → Σ Word (λ cert → Σ Nat (λ t →
        (length cert ≤ evalPoly certBound (length x)) ×
        ((t ≤ timeLimit verifier timeBound x cert) ×
        verifierRun verifier x cert t true)))) ×
      ((Σ Word (λ cert → Σ Nat (λ t →
        (length cert ≤ evalPoly certBound (length x)) ×
        ((t ≤ timeLimit verifier timeBound x cert) ×
        verifierRun verifier x cert t true)))) → language x ≡ true)

InP : Language → Set
InP L = Σ ClassP (λ p → ClassP.language p ≡ L)

InNP : Language → Set
InNP L = Σ ClassNP (λ np → ClassNP.language np ≡ L)

PEqualsNP : Set
PEqualsNP = (L : Language) → InNP L → InP L

PNotEqualsNP : Set
PNotEqualsNP = PEqualsNP → Empty

pToNP : ClassP → ClassNP
pToNP p = record
  { language = ClassP.language p
  ; verifier = ignoreCertificate (ClassP.machine p)
  ; timeBound = ClassP.bound p
  ; certBound = poly 0 0
  ; terminates = λ x cert _ → ClassP.terminates p x
  ; correct = λ x → pair (accept x) (sound x)
  }
  where
    accept : (x : Word) → ClassP.language p x ≡ true →
      Σ Word (λ cert → Σ Nat (λ t →
        (length cert ≤ evalPoly (poly 0 0) (length x)) ×
        ((t ≤ timeLimit (ignoreCertificate (ClassP.machine p)) (ClassP.bound p) x cert) ×
        verifierRun (ignoreCertificate (ClassP.machine p)) x cert t true)))
    accept x hx with ClassP.terminates p x
    ... | t , b , pair ht hr with trans (sym (ClassP.correct p x t b hr)) hx
    ...   | refl = [] , t , pair z≤n (pair ht hr)

    sound : (x : Word) →
      (Σ Word (λ cert → Σ Nat (λ t →
        (length cert ≤ evalPoly (poly 0 0) (length x)) ×
        ((t ≤ timeLimit (ignoreCertificate (ClassP.machine p)) (ClassP.bound p) x cert) ×
        verifierRun (ignoreCertificate (ClassP.machine p)) x cert t true)))) →
      ClassP.language p x ≡ true
    sound x (cert , t , pair _ (pair _ hr)) = ClassP.correct p x t true hr

pSubsetNP : (L : Language) → InP L → InNP L
pSubsetNP L (p , hp) = pToNP p , hp
