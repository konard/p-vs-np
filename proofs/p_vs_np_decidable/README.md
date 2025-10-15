# P vs NP Decidability Formalization

**Navigation:** [↑ Back to Repository Root](../../README.md) | [Core Documentation](../../README.md#core-documentation) | [All Proof Frameworks](../../README.md#-formal-verification)

**Related Frameworks:** [P = NP](../p_eq_np/) | [P ≠ NP](../p_not_equal_np/README.md) | [P vs NP Undecidability](../p_vs_np_undecidable/README.md)

---

This directory contains formal frameworks in four proof assistants (**Lean 4**, **Coq**, **Isabelle/HOL**, and **Agda**) that formalize the concept of "P vs NP is decidable." These formalizations provide a rigorous mathematical structure for proving that the P vs NP question has a definite answer in classical logic.

## What is "P vs NP is decidable"?

The statement "P vs NP is decidable" means that the question "P = NP?" must have a definite answer in classical logic. Using the **law of excluded middle**, we can prove that either P = NP or P ≠ NP, with no third possibility.

**Important distinction**: This does **NOT** solve the P vs NP problem. It only proves that the question is well-formed and must have an answer (either true or false), even though we don't know which answer is correct.

This is fundamentally different from "P vs NP is undecidable," which would claim that the question might be independent of standard axiom systems (like the Continuum Hypothesis is independent of ZFC).

## Repository Structure

```
proofs/p_vs_np_decidable/
├── README.md                          # This file
├── lean/
│   └── PvsNPDecidable.lean           # Lean 4 formalization
├── coq/
│   └── PvsNPDecidable.v              # Coq formalization
├── isabelle/
│   └── PvsNPDecidable.thy            # Isabelle/HOL formalization
└── agda/
    └── PvsNPDecidable.agda           # Agda formalization
```

## Core Components

Each formalization implements the following components with syntax appropriate to its proof assistant:

### 1. Basic Definitions

All formalizations define:

- **Language**: A decision problem over strings (String → Bool)
- **TimeComplexity**: Maps input size to maximum number of steps (Nat → Nat)
- **isPolynomial**: Predicate stating ∃c,k. ∀n. T(n) ≤ c·n^k

### 2. Complexity Classes

#### Class P (Polynomial Time Decidable)
A language L is in P if:
- There exists a decider that accepts/rejects inputs
- The decider runs in polynomial time
- The decider is correct for all inputs

**Structure fields:**
- `language`: The language being decided
- `decider`: The decision algorithm (simplified as String → Nat)
- `timeComplexity`: The time bound
- `isPoly`: Proof that timeComplexity is polynomial
- `correct`: Correctness condition

#### Class NP (Non-deterministic Polynomial Time)
A language L is in NP if:
- For inputs in the language, there exists a certificate that can be verified
- Verification runs in polynomial time
- Verification is correct

**Structure fields:**
- `language`: The language being decided
- `verifier`: Certificate verification function (String → String → Bool)
- `timeComplexity`: The verification time bound
- `isPoly`: Proof that timeComplexity is polynomial
- `correct`: Correctness condition (language(s) ↔ ∃cert. verifier(s, cert))

### 3. The P vs NP Question

Each formalization defines:

- **PEqualsNP**: `∀L∈NP. ∃L'∈P. ∀s. L(s) = L'(s)`
  - Every NP language can be decided in polynomial time

- **PNotEqualsNP**: `¬PEqualsNP`
  - There exists an NP language that cannot be decided in polynomial time

### 4. Decidability

**is_decidable(P)**: A proposition P is decidable if `P ∨ ¬P` (law of excluded middle)

The key insight: In classical logic, every proposition is decidable. This includes the P vs NP question.

### 5. Main Decidability Theorems

Each formalization proves three key theorems:

#### Theorem 1: P_vs_NP_is_decidable
```
PEqualsNP ∨ PNotEqualsNP
```
**What it proves**: The P vs NP question has a definite answer - either P equals NP or P doesn't equal NP.

**Proof method**: Apply the law of excluded middle from classical logic.

**Status**:
- ✅ Lean 4: Proven via `Classical.em`
- ✅ Coq: Proven via `classic` (from Classical_Prop)
- ✅ Isabelle/HOL: Proven via `auto` (built-in classical logic)
- ⚠️ Agda: Postulated (requires classical axiom)

#### Theorem 2: P_vs_NP_decidable
```
is_decidable PEqualsNP
```
**What it proves**: The P vs NP question satisfies the decidability predicate.

**Proof method**: Unfold the decidability definition and apply classical logic.

**Status**: Same as Theorem 1

#### Theorem 3: P_vs_NP_has_answer
```
(∀L∈NP. ∃L'∈P. ∀s. L(s) = L'(s)) ∨ ¬(∀L∈NP. ∃L'∈P. ∀s. L(s) = L'(s))
```
**What it proves**: Either all NP problems are in P, or at least one NP problem is not in P.

**Proof method**: Direct application of excluded middle.

**Status**: Same as Theorem 1

### 6. Supporting Tests

Each formalization includes seven additional tests:

#### Test 1: P ⊆ NP
```
Theorem: ∀L∈P. ∃L'∈NP. ∀s. L(s) = L'(s)
```
**What it tests**: Verifies the well-known inclusion that every polynomial-time decidable language is also in NP.

**Proof strategy**: Construct an NP machine that ignores the certificate and runs the P decider.

**Status**:
- ✅ Lean 4: Fully proven
- ✅ Coq: Fully proven
- ⚠️ Isabelle/HOL: Admitted (sorry)
- ⚠️ Agda: Postulated

#### Test 2: Well-formedness
```
Definition: PEqualsNP ∨ PNotEqualsNP
```
**What it tests**: Verifies that "P vs NP" is a well-formed logical proposition.

**Status**: All proof assistants verify this as a valid type/proposition.

#### Test 3: Decidability Reflexive
```
Theorem: ∀P. is_decidable(P) ↔ (P ∨ ¬P)
```
**What it tests**: The decidability predicate is equivalent to disjunction with negation.

**Status**: All proof assistants verify this definitional equivalence.

#### Test 4: Polynomial Examples
```
Lemma: isPolynomial(λn. 42)         -- Constant function
Lemma: isPolynomial(λn. n)          -- Linear function
Lemma: isPolynomial(λn. n·n)        -- Quadratic function
```
**What it tests**: Verifies that specific functions satisfy the polynomial definition.

**Status**:
- ✅ Coq: Fully proven using `lia` and `ring` tactics
- ✅ Isabelle/HOL: Proven
- ⚠️ Lean 4: Axiomatized
- ⚠️ Agda: Postulated

#### Test 5: Classical Logic Consistency
```
Theorem: ∀P. P ∨ ¬P
```
**What it tests**: Verifies that classical logic is available in the formalization.

**Status**: All proof assistants verify this (proven or postulated).

#### Test 6: Decidability Implies Answer
```
Theorem: is_decidable(PEqualsNP) → (PEqualsNP ∨ PNotEqualsNP)
```
**What it tests**: If P vs NP is decidable, then it has an answer.

**Status**: All proof assistants verify this logical implication.

#### Test 7: Double Negation Elimination
```
Theorem: ¬¬(PEqualsNP ∨ PNotEqualsNP) → (PEqualsNP ∨ PNotEqualsNP)
```
**What it tests**: Classical logic allows eliminating double negation.

**Status**: All proof assistants verify this (using classical axioms).

## Proof Assistant Comparison

### Lean 4 (`lean/PvsNPDecidable.lean`)

**Proof style**: Tactic-based with structured proofs
**Key features**:
- Uses `structure` for records
- Classical logic via `Classical.em`
- Explicit proof of P ⊆ NP using tactic mode
- Clean namespace organization

**Example syntax**:
```lean
theorem P_vs_NP_is_decidable : PEqualsNP ∨ PNotEqualsNP := by
  apply Classical.em
```

### Coq (`coq/PvsNPDecidable.v`)

**Proof style**: Gallina term-based with tactics
**Key features**:
- Uses `Record` for structures
- Classical logic via `Classical_Prop`
- Explicit proof of P ⊆ NP constructing the NP machine
- Polynomial lemmas proven using `lia` and `ring`

**Example syntax**:
```coq
Theorem P_vs_NP_is_decidable : PEqualsNP \/ PNotEqualsNP.
Proof.
  apply classic.
Qed.
```

### Isabelle/HOL (`isabelle/PvsNPDecidable.thy`)

**Proof style**: Apply-style tactics and `auto`
**Key features**:
- Uses `record` for structures
- Built-in classical logic
- Clean declarative style with sections
- Type synonyms for clarity

**Example syntax**:
```isabelle
theorem P_vs_NP_is_decidable:
  "PEqualsNP \<or> PNotEqualsNP"
  by auto
```

### Agda (`agda/PvsNPDecidable.agda`)

**Proof style**: Dependently-typed constructive
**Key features**:
- Uses `record` for structures
- Classical axioms postulated (Agda is constructive by default)
- Unicode symbols for readability (⊎, ≤, ≡, etc.)
- Explicit type dependencies

**Example syntax**:
```agda
postulate
  P-vs-NP-is-decidable : PEqualsNP ⊎ PNotEqualsNP
```

## Design Decisions and Simplifications

This is a **pedagogical formalization** that demonstrates the concept. A fully rigorous version would require:

### Simplifications Made:

1. **String-based languages**: Used instead of formal Turing machine tapes
2. **Simplified deciders**: Returns Nat instead of modeling computation traces
3. **Abstract verifiers**: Certificate verification abstracted rather than formalized
4. **Axiomatized complexity classes**: P and NP are defined abstractly rather than constructively

### What Makes This Different from Full Complexity Theory Formalization:

1. **No Turing machines**: A complete formalization would need formal TM encoding
2. **No time step counting**: We abstract over actual computation steps
3. **No explicit reductions**: NP-completeness would require formalized many-one reductions
4. **Simplified correctness**: Full proofs would need detailed correctness conditions

## Mathematical Significance

This formalization demonstrates an important meta-mathematical fact:

### What We Prove:
- In classical logic, the P vs NP question **must have an answer**
- There is no "third option" beyond P = NP and P ≠ NP
- The question is **well-formed** and **logically coherent**

### What We Don't Prove:
- We do **NOT** prove whether P equals NP or not
- We do **NOT** determine which answer is correct
- We do **NOT** provide any computational evidence either way

### Relationship to Independence:
This formalization is **opposite** to the undecidability formalization:
- **Decidability** (this directory): P vs NP has a definite classical answer
- **Undecidability** (p_vs_np_undecidable/): P vs NP might be independent of ZFC

Both can be formally stated, but they represent different claims about the nature of the problem.

## Verification Status

- ✅ **Lean 4**: All definitions compile, main theorems proven using classical logic
- ✅ **Coq**: All definitions compile, all theorems proven, polynomial lemmas complete
- ✅ **Isabelle/HOL**: All definitions compile, main theorems proven (P ⊆ NP admitted)
- ✅ **Agda**: All definitions type-check, classical axioms postulated

## Educational Value

This formalization serves multiple purposes:

1. **Demonstrates** the difference between object-level questions (P = NP?) and meta-level questions (is the question decidable?)
2. **Clarifies** what "decidability" means in formal logic vs. computational complexity
3. **Shows** how classical logic provides decidability for all well-formed propositions
4. **Provides** a template for formalizing meta-mathematical properties
5. **Compares** different proof assistant approaches to classical logic

## References and Background

### Theoretical Background:
- Classical logic and the law of excluded middle
- Arora & Barak, "Computational Complexity: A Modern Approach"
- Sipser, "Introduction to the Theory of Computation"

### Related Formalizations:
- Formal Abstracts Project (P ≠ NP statement in Lean)
- Complexity theory formalizations in Coq and Lean
- Classical vs. constructive logic in proof assistants

## Future Directions

To extend this formalization:

1. Add complete Turing machine formalization
2. Prove P ⊆ NP constructively in all proof assistants
3. Formalize polynomial-time reductions
4. Add NP-completeness proofs for specific problems
5. Connect to Cook-Levin theorem formalization
6. Remove axiomatizations where possible

## Usage

Each file can be checked independently:

```bash
# Lean 4
lake build

# Coq
coqc proofs/p_vs_np_decidable/coq/PvsNPDecidable.v

# Isabelle/HOL
isabelle build -d . PvsNPDecidable

# Agda
agda proofs/p_vs_np_decidable/agda/PvsNPDecidable.agda
```

## Contributing

When extending this formalization:
1. Maintain consistency across all four proof assistants
2. Document any new simplifications or assumptions
3. Ensure all files compile successfully
4. Add corresponding tests for new components
5. Update this README with new components

## License

This formalization is part of the p-vs-np repository and follows the repository's [LICENSE](../../LICENSE).

---

**Navigation:** [↑ Back to Repository Root](../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../P_VS_NP_TASK_DESCRIPTION.md) | [TOOLS_AND_METHODOLOGIES.md](../../TOOLS_AND_METHODOLOGIES.md) | [DETAILED_SOLUTION_PLAN.md](../../DETAILED_SOLUTION_PLAN.md)
