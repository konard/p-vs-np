# P ⊆ NP: Formal Proof

**Navigation:** [↑ Back to Repository Root](../../README.md) | [Core Documentation](../../README.md#core-documentation)

---

This directory contains formal proofs in four proof assistants (**Lean 4**, **Coq**, **Isabelle/HOL**, and **Agda**) of the fundamental theorem:

## **P ⊆ NP**

**Theorem**: Every language decidable in polynomial time is also verifiable in polynomial time with a certificate.

This is a well-known, foundational result in computational complexity theory.

## Repository Structure

```
proofs/p_vs_np_decidable/
├── README.md                # This file
├── lean/
│   └── PSubsetNP.lean      # Lean 4 proof
├── coq/
│   └── PSubsetNP.v         # Coq proof
├── isabelle/
│   └── PSubsetNP.thy       # Isabelle/HOL proof
└── agda/
    └── PSubsetNP.agda      # Agda proof
```

## What This Proves

**Statement**: ∀L ∈ P. ∃L' ∈ NP. ∀s. L(s) = L'(s)

**Meaning**: For every language L in P (polynomial-time decidable), there exists a corresponding language L' in NP (polynomial-time verifiable) such that L and L' accept exactly the same strings.

**Proof Strategy**: Given a language L in P with a polynomial-time decider, construct an NP verifier that:
1. Ignores the certificate input
2. Directly runs the P decider on the input string
3. Accepts if and only if the P decider accepts

Since the P decider runs in polynomial time, the NP verifier also runs in polynomial time, proving that L is in NP.

## Core Definitions

Each formalization defines:

### 1. Basic Types
- **Language**: A decision problem over strings (String → Bool)
- **TimeComplexity**: Maps input size to maximum steps (Nat → Nat)
- **isPolynomial**: Predicate stating ∃c,k. ∀n. T(n) ≤ c·n^k

### 2. Complexity Classes

**Class P** (Polynomial-time decidable):
- `language`: The language being decided
- `decider`: Decision algorithm (String → Nat)
- `timeComplexity`: Time bound
- `isPoly`: Proof that time is polynomial
- `correct`: Correctness property

**Class NP** (Non-deterministic polynomial-time):
- `language`: The language being decided
- `verifier`: Certificate verification (String → String → Bool)
- `timeComplexity`: Verification time bound
- `isPoly`: Proof that time is polynomial
- `correct`: Correctness property (∃certificate iff accepted)

## Proof Status

All four proof assistants have **complete, verified proofs** of P ⊆ NP:

- ✅ **Lean 4**: Fully proven using tactic mode
- ✅ **Coq**: Fully proven constructing explicit NP machine
- ✅ **Isabelle/HOL**: Fully proven using structured proof
- ✅ **Agda**: Fully proven using dependent types

## Proof Assistant Comparison

### Lean 4 (`lean/PSubsetNP.lean`)

**Proof style**: Tactic-based with structured proofs

**Example**:
```lean
theorem pSubsetNP : ∀ L : ClassP, ∃ L' : ClassNP, ∀ s : String, L.language s = L'.language s := by
  intro L
  let npLang : ClassNP := {
    language := L.language
    verifier := fun s _ => L.language s  -- Ignore certificate
    ...
  }
  exists npLang
  intro s
  rfl
```

### Coq (`coq/PSubsetNP.v`)

**Proof style**: Gallina with tactics

**Example**:
```coq
Theorem pSubsetNP : forall L : ClassP, exists L' : ClassNP,
  forall s : string, p_language L s = np_language L' s.
Proof.
  intro L.
  exists (mkClassNP
    (p_language L)
    (fun s _ => p_language L s)  (* Verifier ignores certificate *)
    ...
  ).
  intro s.
  reflexivity.
Qed.
```

### Isabelle/HOL (`isabelle/PSubsetNP.thy`)

**Proof style**: Structured declarative proofs

**Example**:
```isabelle
lemma pSubsetNP:
  "∀L::ClassP. ∃L'::ClassNP. ∀s. p_language L s = np_language L' s"
proof -
  {
    fix L :: ClassP
    define L' where "L' = ⟨np_language = p_language L, ...⟩"
    have "∀s. p_language L s = np_language L' s" by (simp add: L'_def)
    hence "∃L'::ClassNP. ∀s. p_language L s = np_language L' s" by blast
  }
  thus ?thesis by auto
qed
```

### Agda (`agda/PSubsetNP.agda`)

**Proof style**: Dependently-typed constructive

**Example**:
```agda
pSubsetNP : ∀ (L : ClassP) → ∃[ L' ] (∀ (s : String) → ClassP.language L s ≡ ClassNP.language L' s)
pSubsetNP L = npLang , proof
  where
    npLang : ClassNP
    npLang = record { language = pLang ; verifier = λ s cert → pLang s ; ... }

    proof : ∀ (s : String) → pLang s ≡ ClassNP.language npLang s
    proof s = refl
```

## Mathematical Significance

This proof establishes a **fundamental relationship** in complexity theory:

- **P ⊆ NP** is the basis for the P vs NP question
- Without this inclusion, P = NP would be trivially false
- This shows that verification is at least as powerful as decision
- It's the foundation for understanding NP-completeness

## What This Does NOT Prove

- ❌ Whether P = NP or P ≠ NP
- ❌ Whether the inclusion is strict (P ⊂ NP)
- ❌ Anything about the reverse direction (NP ⊆ P)

## Verification

Each file can be checked independently:

```bash
# Lean 4
lake build

# Coq
coqc proofs/p_vs_np_decidable/coq/PSubsetNP.v

# Isabelle/HOL
isabelle build -d . PSubsetNP

# Agda
agda proofs/p_vs_np_decidable/agda/PSubsetNP.agda
```

## References

- Arora & Barak, "Computational Complexity: A Modern Approach"
- Sipser, "Introduction to the Theory of Computation"
- Papadimitriou, "Computational Complexity"

---

**Navigation:** [↑ Back to Repository Root](../../README.md)
