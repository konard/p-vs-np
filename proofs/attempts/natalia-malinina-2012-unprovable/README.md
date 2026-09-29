# Natalia L. Malinina (2012) - P vs NP is Unprovable in ZFC

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 95
- **Author**: Natalia L. Malinina
- **Year**: 2012
- **Claim**: P vs NP is **unprovable** (independence from ZFC)
- **Status**: **REFUTED** - The argument contains fundamental gaps and does not constitute a valid independence proof
- **Source**: [Woeginger's P vs NP Attempts List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #95)
- **Paper**: "On the unprovability of the P ≠ NP conjecture" (2012)

---

## Summary

Natalia L. Malinina's 2012 paper attempts to demonstrate that the question of whether P equals NP is undecidable (unprovable) within standard axiomatic set theory (ZFC). The approach draws on Gödelian incompleteness arguments, claiming that the P vs NP question can be shown to be independent of ZFC by constructing a self-referential statement that, if provable, leads to a contradiction.

The core argument attempts to use a diagonalization-style construction to show that any proof of P ≠ NP (or P = NP) would allow the construction of a self-referential algorithm that contradicts its own existence, analogous to the halting problem's undecidability.

---

## The Core Argument

### Step 1: Self-Referential Algorithm Construction

Malinina constructs a hypothetical algorithm A that:
1. Takes as input any algorithm B and a problem instance x
2. Simulates B on x using a "polynomial-time oracle"
3. Returns the opposite of what B would return

The argument claims that if P ≠ NP were provable, one could construct A as a polynomial-time algorithm that solves all NP problems by "inverting" any proposed P algorithm.

### Step 2: Gödelian Diagonalization

The paper applies a diagonalization argument:
- Assume, for contradiction, that ZFC proves P ≠ NP
- Construct a statement φ that encodes "φ is not provable in ZFC + [P ≠ NP]"
- By Gödel's second incompleteness theorem, if ZFC is consistent, φ must be true but unprovable
- This contradicts the assumption that ZFC proves P ≠ NP

### Step 3: Independence Claim

From the diagonalization construction, Malinina concludes:
- Neither P = NP nor P ≠ NP can be proved from ZFC axioms alone
- Therefore, P vs NP is independent of ZFC (analogous to the Continuum Hypothesis)

### Claimed Significance

If correct, this would have major implications:
- The P vs NP problem would be fundamentally unresolvable within standard mathematics
- A new axiomatic system would be needed to settle the question
- The problem would join CH and other famous independent statements

---

## The Errors

This argument contains **multiple fundamental logical errors** that invalidate the independence claim:

### 1. **Conflation of Computational and Meta-mathematical Undecidability**

**The Flaw**: Malinina conflates Turing-undecidability (the halting problem) with proof-theoretic independence (Gödel incompleteness).

**Why It's Wrong**:
- The halting problem is undecidable in the sense that no algorithm can solve it
- Gödel incompleteness says some statements are unprovable from given axioms
- These are distinct concepts: a statement can be computationally hard to decide yet still be provable or refutable in ZFC
- P vs NP asks about an algorithm's existence, not about self-referential provability
- Applying diagonalization from Gödel's theorem to the P vs NP question requires careful formalization that is missing from the paper

### 2. **Invalid Self-Referential Construction**

**The Flaw**: The "inverting algorithm" A does not work as described.

**Why It's Wrong**:
- Algorithm A as described would need to solve an arbitrary NP problem in polynomial time to "invert" a proposed P algorithm
- This is circular: A uses polynomial-time oracle access to NP, but that oracle access is exactly what we're trying to prove or disprove exists
- The self-reference does not create the claimed contradiction; it merely assumes polynomial-time oracle access, which is the very assumption being questioned
- Compare: the halting problem's undecidability proof works because we can effectively simulate any TM; no such effective simulation of NP oracles in P is known

### 3. **Misapplication of Gödel's Incompleteness Theorem**

**The Flaw**: Gödel's theorem applies to statements that can be encoded as arithmetic sentences; the application here is not correctly formalized.

**Why It's Wrong**:
- Gödel's second incompleteness theorem says: if ZFC is consistent, it cannot prove its own consistency
- The statement "P ≠ NP" is not of the form "ZFC is consistent" — it is a statement about the existence of polynomial-time algorithms
- To apply Gödelian incompleteness, one must first formalize P vs NP as an arithmetic statement and show it has the self-referential structure required
- Malinina does not provide this formalization; the analogy is informal and does not establish actual independence

### 4. **Missing Model-Theoretic Argument**

**The Flaw**: A valid independence proof requires constructing two models: one where P = NP holds and one where P ≠ NP holds.

**Why It's Wrong**:
- Independence of a statement S from ZFC requires:
  - A model M₁ of ZFC where S is true
  - A model M₂ of ZFC where S is false
- Malinina provides no such model construction
- Without exhibiting explicit models, the independence claim is merely an assertion, not a proof
- Compare to Cohen's proof of the independence of the Continuum Hypothesis, which required the invention of forcing to construct the needed models

### 5. **Complexity-Theoretic Context Ignored**

**The Flaw**: The paper does not engage with known barriers to P vs NP proofs.

**Why It's Wrong**:
- Any valid proof attempt (including independence proofs) must address:
  - **Relativization**: P vs NP relativizes, meaning any proof technique must distinguish between relativizing and non-relativizing arguments
  - **Natural Proofs**: The Razborov-Rudich barrier limits circuit lower bound proofs
  - **Algebrization**: Extensions of relativization that further restrict proof methods
- Malinina's approach does not engage with any of these barriers
- A genuine independence proof would need to show why these barriers do not apply

### 6. **Circularity in the Core Argument**

**The Flaw**: The argument assumes what it is trying to prove.

**Why It's Wrong**:
- The construction of algorithm A implicitly assumes access to NP-oracle queries that can be answered in polynomial time
- This is equivalent to assuming P = NP (or that P = NP^P), which is the very statement whose provability is being questioned
- The argument is therefore circular: it uses P = NP to show P vs NP is unprovable

---

## What Would Constitute a Valid Independence Proof

To validly prove P vs NP is independent of ZFC, one would need:

### For Consistency of ZFC + [P = NP]:
1. **Construct a model** M₁ of ZFC where all NP problems have polynomial-time algorithms
2. **Verify** M₁ satisfies all ZFC axioms
3. **Verify** the notions of "polynomial time" and "NP" are correctly formalized in M₁

### For Consistency of ZFC + [P ≠ NP]:
1. **Construct a model** M₂ of ZFC where some NP problem has no polynomial-time algorithm
2. **Verify** M₂ satisfies all ZFC axioms
3. **Verify** that the complexity-theoretic notions behave correctly in M₂

### Key Challenges:
- **Absoluteness**: Many complexity-theoretic notions are absolute across set-theoretic models, making it hard to change their truth value by model manipulation
- **Formalization**: P and NP must be precisely formalized as Σ₂-statements (or similar) in the language of set theory
- **Relativization Barriers**: Any independence proof must overcome known barriers

---

## Expert Analysis

Several experts in computational complexity and mathematical logic have noted why independence arguments for P vs NP face significant obstacles:

- **Scott Aaronson** has written extensively on why P vs NP is unlikely to be independent of ZFC, noting that independence results for "natural" mathematical statements are rare and require extraordinary evidence
- **Russell Impagliazzo** and others have noted that the concrete, combinatorial nature of P vs NP makes independence unlikely (though not impossible)
- The known barriers (relativization, natural proofs, algebrization) apply to *proofs* of P ≠ NP, not to independence proofs, making this a subtly different challenge

---

## Formal Verification

This directory contains formalizations in Lean 4 and Rocq that expose the structural errors:

### Implementations

1. **[Lean 4 Proof Formalization](proof/lean/MalininaProof.lean)** - Forward formalization of Malinina's claimed argument
2. **[Rocq Proof Formalization](proof/rocq/MalininaProof.v)** - Rocq version of the forward formalization
3. **[Lean 4 Refutation](refutation/lean/MalininaRefutation.lean)** - Lean formalization showing the gaps
4. **[Rocq Refutation](refutation/rocq/MalininaRefutation.v)** - Rocq version of the refutation

### What the Formalizations Show

Each formalization:
- ✅ Defines the structure of the attempted argument
- ✅ Identifies the circular assumption in the algorithm construction
- ✅ Shows where Gödel's theorem is misapplied
- ✅ Demonstrates what a valid independence proof would require
- ✅ Makes explicit the missing model-theoretic components

---

## Educational Value

Despite being incorrect, formalizing this attempt illustrates:

1. **The Gap Between Computability and Provability**: Undecidability and unprovability are distinct concepts
2. **Self-Reference Requires Care**: Diagonalization arguments are powerful but must be applied carefully
3. **Independence Proofs Are Hard**: Valid independence results (like Cohen's) require major new tools
4. **Complexity Barriers**: The known barriers to P vs NP proofs are real obstacles

---

## References

### Primary Source
- **Malinina, N.L.** (2012). "On the unprovability of the P ≠ NP conjecture." *Available via Woeginger's P vs NP attempts list.*

### Woeginger's List
- **Woeginger, G. J.** "The P-versus-NP page" (Entry #95)
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Background on Incompleteness and Independence
- **Gödel, K.** (1931). "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I."
- **Cohen, P.** (1963). "The independence of the continuum hypothesis." *PNAS* 50(6), 1143-1148.
- **Kunen, K.** (2011). *Set Theory*. College Publications.

### P vs NP Independence Discussion
- **Aaronson, S.** (2011). "Is P vs. NP formally independent?" Blog post: https://scottaaronson.blog/?p=1948
- **Aaronson, S.** (2003). "Is P Versus NP Formally Independent?"

### Complexity Theory Barriers
- **Baker, T., Gill, J., Solovay, R.** (1975). "Relativizations of the P=NP question." *SIAM J. Comput.* 4(4), 431-442.
- **Razborov, A., Rudich, S.** (1997). "Natural proofs." *JCSS* 55(1), 24-35.
- **Aaronson, S., Wigderson, A.** (2009). "Algebrization: A new barrier in complexity theory." *TOCT* 1(1).

---

## Related Attempts in This Repository

- **[Da Costa & Doria (2003)](../ncada-costa-fa-doria-2003-unprovable/)** - Another attempt to prove P vs NP is unprovable in ZFC, using exotic definitions

---

**Part of**: [Issue #480](https://github.com/konard/p-vs-np/issues/480) | **Parent Issue**: [#44 - Test all P vs NP attempts formally](https://github.com/konard/p-vs-np/issues/44)
