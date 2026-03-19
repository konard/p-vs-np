# Experimental Proof Attempt: P vs NP Undecidability (Issue #7)

**Created**: 2026-01-18
**Status**: Exploratory Research
**Goal**: Investigate whether P vs NP could be independent of ZFC

---

## Executive Summary

This document explores an experimental attempt to prove that P vs NP is undecidable (independent of ZFC). **Critical finding**: The attempt faces a fundamental insurmountable obstacle in the form of **Shoenfield's absoluteness theorem**, which strongly suggests P vs NP cannot be independent of ZFC.

**Conclusion**: While we can formalize the concept of independence and explore theoretical approaches, a rigorous proof that P vs NP is independent of ZFC is almost certainly impossible due to the arithmetic nature of the statement.

---

## 1. The P vs NP Statement's Logical Form

### 1.1 Complexity-Theoretic Formulation

P vs NP asks: "Does P = NP?" which expands to:

```
P = NP  ⟺  ∀L ∈ NP. ∃M. M decides L in polynomial time
```

### 1.2 Arithmetic Translation

This can be encoded in the language of arithmetic (Peano Arithmetic or ZFC) as:

```
P = NP  ⟺  ∀k. ∀V. [V is a poly-time verifier for language L_k]
              →  ∃D. [D is a poly-time decider for L_k]
```

More precisely, expanding the definitions:

```
P = NP  ⟺  ∀k, V, p_V. [Polynomial(p_V) ∧ V verifies L_k in time p_V]
              →  ∃D, p_D. [Polynomial(p_D) ∧ D decides L_k in time p_D]
```

### 1.3 Quantifier Structure: Π₂⁰

The key observation: P vs NP has the logical form:

```
∀x. ∃y. φ(x, y)
```

where φ is quantifier-free and involves only arithmetic operations.

This makes P vs NP a **Π₂⁰ statement** in the arithmetical hierarchy:
- Outer quantifier: ∀ (over verifiers, languages, polynomial bounds)
- Inner quantifier: ∃ (over deciders, polynomial bounds)
- No further quantifier alternations

---

## 2. Shoenfield's Absoluteness Theorem

### 2.1 Statement of the Theorem

**Shoenfield's Absoluteness Theorem** (1961):

> If φ is a Σ¹₃ (or Π¹₃) formula in the analytical hierarchy, then for any transitive models M and N of ZFC such that M ⊆ N and M and N have the same ordinals:
>
> M ⊨ φ  ⟺  N ⊨ φ

**Crucially**, this applies to all **Π₂⁰** and **Σ₂⁰** arithmetic statements (which are much lower in the hierarchy than Π¹₃).

### 2.2 Application to P vs NP

Since P vs NP is a Π₂⁰ arithmetic statement:

1. P vs NP is expressible in the language of arithmetic
2. By Shoenfield's theorem, P vs NP is **absolute** across all models of ZFC with the same ordinals
3. This means: If P = NP in one model of ZFC, then P = NP in **all** models with the same ordinals
4. Similarly for P ≠ NP

### 2.3 Implication for Independence

**Key Consequence**: For P vs NP to be independent of ZFC, we would need:
- Model M₁ of ZFC where P = NP
- Model M₂ of ZFC where P ≠ NP

But Shoenfield's theorem implies this is **impossible** (assuming M₁ and M₂ have the same ordinals, which forcing extensions and most model constructions preserve).

---

## 3. Potential Loopholes (All Unlikely)

Despite Shoenfield's theorem, let's explore theoretical loopholes:

### 3.1 Loophole 1: Different Ordinals

**Idea**: Construct models with **different ordinals** where P vs NP differs.

**Problems**:
- Most natural models (forcing extensions, inner models like L) preserve ordinals
- Models with different ordinals are drastically different (different notion of "countable")
- P vs NP is about *finite* computation - ordinals shouldn't matter
- Even in models with different ordinals, the finite part (standard model of arithmetic) is typically the same

**Verdict**: Theoretically possible but highly implausible. The truth of P vs NP should depend only on standard finite computation, not on set-theoretic ordinals.

### 3.2 Loophole 2: Non-Standard Models of Arithmetic

**Idea**: Study P vs NP in non-standard models of PA (with non-standard "integers").

**Approach**:
- In non-standard models, "polynomial time" might include non-standard polynomials
- Non-standard "TM that runs in polynomial time" might exist
- Could P vs NP have different truth values in standard vs non-standard models?

**Analysis**:
- The standard formulation of P vs NP refers to standard integers
- Even if non-standard models behave differently, the **standard part** (what we care about) is the same
- Shoenfield's theorem still applies to the arithmetic truth

**Verdict**: Interesting for understanding the formalization, but doesn't evade absoluteness for the standard interpretation.

### 3.3 Loophole 3: Computational Content Beyond Set Theory

**Idea**: Perhaps "polynomial-time computation" has content not fully captured by ZFC.

**Philosophical Argument**:
- Computation might be a primitive notion beyond sets
- Physical Church-Turing thesis might require axioms beyond ZFC
- Alternative foundations (type theory, category theory) might give different answers

**Counter-Arguments**:
- Turing machines are fully formalizable in ZFC (or even PA)
- Polynomial-time computation is a well-defined mathematical concept
- No evidence that alternative foundations would change P vs NP

**Verdict**: Philosophically interesting but mathematically unconvincing.

### 3.4 Loophole 4: Formalization Uses Higher Complexity

**Idea**: Perhaps the "natural" formalization of P vs NP is actually Π¹₁ (analytical) rather than Π₂⁰?

**Investigation**:
- Standard formalization: quantify over Turing machines (can be coded as integers)
- This gives Π₂⁰ statement
- Could we need to quantify over *sets* of Turing machines, raising complexity?

**Analysis**:
- No, standard formalization is definitely Π₂⁰
- Quantification over TMs can be coded arithmetically
- Polynomial-time is arithmetically definable

**Verdict**: No escape via this route.

---

## 4. Forcing Attempt (Doomed by Absoluteness)

Despite knowing it's doomed, let's sketch what a forcing approach would look like:

### 4.1 Naive Forcing Idea

**Goal**: Construct forcing extension M[G] where P = NP differs from ground model M.

**Approach**:
1. Let M be a countable transitive model of ZFC where P ≠ NP (assuming P ≠ NP is true)
2. Define forcing notion P that adds "generic polynomial-time algorithm for SAT"
3. Force with P to get M[G]
4. Hope: In M[G], there exists polynomial-time algorithm for SAT (so P = NP in M[G])

### 4.2 Why This Fails

**Obstacle**: Shoenfield's absoluteness

- M and M[G] have the same ordinals (forcing preserves ordinals)
- P vs NP is Π₂⁰
- By Shoenfield: M ⊨ "P = NP" ⟺ M[G] ⊨ "P = NP"
- **Therefore**: Cannot change truth value of P vs NP via forcing

**The Mechanism**:
- Even if we "add" a polynomial-time SAT solver to M[G], it's not a "real" polynomial-time algorithm
- The generic object G might give us "pseudo-polynomial" algorithm that works for non-standard inputs
- For **standard** finite strings and **standard** polynomial time, the truth is absolute

### 4.3 Comparison to Continuum Hypothesis

**Why CH Can Be Forced**:
- CH is Π¹₂ statement (involves quantification over reals/sets)
- CH is **not** absolute (not covered by Shoenfield)
- Forcing can add reals and change cardinalities

**Why P vs NP Cannot Be Forced**:
- P vs NP is Π₂⁰ (arithmetic, quantifies over integers/TMs)
- P vs NP **is** absolute (covered by Shoenfield)
- Forcing cannot change arithmetic truths about standard integers

---

## 5. Bounded Arithmetic Approach

### 5.1 Weaker Theories

**More Promising Direction**: Study independence from **bounded arithmetic** theories.

**Theories**:
- **S₂¹**: Theory formalizing polynomial-time reasoning (corresponds to NP)
- **T₂¹**: Theory formalizing strictly polynomial-time reasoning (corresponds to P)
- **PV**: Cook's theory of polynomial-time functions

**Question**: Can S₂¹ prove P = NP or P ≠ NP?

### 5.2 Krajiček-Pudlák Correspondence

**Known Results**:
- S₂¹ can formalize NP computations
- T₂¹ can formalize P computations
- S₂¹ = T₂¹ would imply P = NP (informal correspondence)

**Unprovability Conjecture**:
- S₂¹ cannot prove "S₂¹ = T₂¹" (analogous to Gödel incompleteness)
- This suggests S₂¹ cannot resolve P vs NP

### 5.3 Independence from Bounded Arithmetic?

**Feasibility**: More plausible than independence from ZFC

**What It Would Mean**:
- P vs NP is independent of weak theories like S₂¹
- But still provable/refutable in stronger theories (PA, ZFC)
- Analogous to Paris-Harrington theorem (unprovable in PA but true in ZFC)

**Research Value**:
- Understanding proof-theoretic strength of P vs NP
- Connecting to proof complexity
- Doesn't solve millennium problem but illuminates structure

---

## 6. Experimental Formalization Attempt

### 6.1 What We Can Formalize

Even though full independence proof is impossible, we can formalize:

1. **The concept of independence** (structure representing unprovability)
2. **Hypothetical forcing construction** (showing what would be needed)
3. **Shoenfield's theorem** (explaining why it fails)
4. **Bounded arithmetic theories** (exploring weaker systems)

### 6.2 Educational Value

Formalizing the *attempt* has value:
- Demonstrates why P vs NP is likely decidable in ZFC
- Illustrates the power of Shoenfield's absoluteness
- Provides template for studying actual independence results
- Clarifies the arithmetic nature of P vs NP

### 6.3 Formalization Structure

```lean
-- Hypothetical forcing construction (known to fail due to Shoenfield)
structure ForcingAttempt where
  groundModel : Model ZFC
  forcingNotion : ℙ
  genericFilter : ℙ → Filter
  extension : Model ZFC
  -- Key property: ordinals preserved
  ordinalsPreserved : groundModel.Ordinals = extension.Ordinals

-- Shoenfield's absoluteness (blocks forcing approach)
theorem shoenfield_absoluteness
  (M N : Model ZFC)
  (φ : Π₂⁰_Formula)
  (h : M.Ordinals = N.Ordinals) :
  M ⊨ φ ↔ N ⊨ φ := sorry

-- Application to P vs NP
theorem pvsnp_is_absolute :
  ∀ M N : Model ZFC,
  M.Ordinals = N.Ordinals →
  (M ⊨ "P = NP" ↔ N ⊨ "P = NP") := by
  intros M N h
  apply shoenfield_absoluteness
  exact h

-- Conclusion: Independence from ZFC is implausible
theorem independence_unlikely :
  ¬∃ (M N : Model ZFC),
    M.Ordinals = N.Ordinals ∧
    M ⊨ "P = NP" ∧
    N ⊨ "P ≠ NP" := by
  intro ⟨M, N, hOrd, hM, hN⟩
  have : M ⊨ "P = NP" ↔ N ⊨ "P = NP" := pvsnp_is_absolute M N hOrd
  -- Contradiction: hM says M ⊨ "P=NP" but hN says N ⊨ "P≠NP"
  cases this
  contradiction
```

---

## 7. Realistic Assessment

### 7.1 Probability Estimates

- **P vs NP independent of ZFC**: < 1%
- **P vs NP independent of bounded arithmetic (S₂¹)**: 20-30%
- **Valuable insights from this investigation**: 90%+

### 7.2 What We Learn

Even though independence from ZFC is implausible:

1. **P vs NP has a definite answer** (by Shoenfield)
2. **The answer is provable in ZFC** (if we could find the proof)
3. **Barriers are about proof difficulty**, not mathematical undecidability
4. **Focus should be on direct proof**, not independence

### 7.3 Where to Direct Effort

**More Promising**:
- Direct proof attempts for P ≠ NP
- Circuit lower bounds
- Geometric complexity theory
- Proof complexity lower bounds

**Less Promising**:
- Trying to prove independence from ZFC
- Forcing constructions for P vs NP
- Set-theoretic approaches to complexity

---

## 8. Conclusion

### 8.1 Summary of Findings

**Research Question**: Is P vs NP independent of ZFC?

**Answer**: Almost certainly **no**, due to Shoenfield's absoluteness theorem.

**Key Points**:
1. P vs NP is a Π₂⁰ arithmetic statement
2. Shoenfield's theorem makes Π₂⁰ statements absolute across models
3. Standard independence techniques (forcing, inner models) cannot change P vs NP
4. This is fundamentally different from genuinely independent statements like CH

### 8.2 Positive Outcome

This investigation **strengthens** the case for P vs NP being a well-defined mathematical question with a definite answer. The barriers to solving P vs NP are about:
- Proof difficulty (technical challenge)
- Proof length (possibly super-polynomial)
- Limitations of current techniques

But NOT about:
- Mathematical undecidability
- Set-theoretic independence
- Fundamental unprovability

### 8.3 Implications

**For the Millennium Problem**:
- There exists a proof of either P = NP or P ≠ NP in ZFC
- Finding that proof is extremely difficult but theoretically possible
- No "escape hatch" via independence

**For Research Strategy**:
- Focus on direct proof attempts
- Develop new techniques that overcome known barriers
- Study proof complexity to understand why the proof is hard to find

### 8.4 Educational Value of This Attempt

Attempting to prove independence has value:
- Deepens understanding of P vs NP's logical structure
- Illustrates power of Shoenfield's absoluteness
- Clarifies relationship between complexity and logic
- Demonstrates rigorous mathematical reasoning about meta-questions

---

## References

1. **Shoenfield, J. R.** (1961). "The problem of predicativity." In: Essays on the Foundations of Mathematics.

2. **Arora, S., & Barak, B.** (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.

3. **Krajíček, J.** (1995). *Bounded Arithmetic, Propositional Logic, and Complexity Theory*. Cambridge University Press.

4. **Kunen, K.** (2011). *Set Theory*. College Publications. (For forcing and model theory)

5. **Aaronson, S.** (2016). "P vs NP" survey. In: *Open Problems in Mathematics*.

6. **Ben-David, S., & Halevi, S.** (1992). "On the independence of P versus NP." Technical Report. (Discusses why independence is unlikely)

---

## Appendix: Alternative Avenues

### A.1 Proof Complexity

Study whether P ≠ NP has super-polynomially long proofs in various systems:
- Extended Frege systems
- Resolution
- Cutting planes

**Value**: Understanding proof difficulty even if statement is decidable.

### A.2 Reverse Mathematics

Determine minimal axioms needed for P vs NP:
- Which subsystem of second-order arithmetic suffices?
- Is P vs NP equivalent to some standard axiom system?

**Value**: Classifying proof-theoretic strength.

### A.3 Bounded Arithmetic Independence

Serious investigation of independence from S₂¹:
- More plausible than ZFC independence
- Connects to proof complexity
- Illuminates structure of polynomial-time reasoning

**Value**: Could be achievable and mathematically significant.

---

**Final Note**: While we cannot prove P vs NP is independent of ZFC, this investigation clarifies that P vs NP has a definite mathematical answer that is provable in principle. The challenge is finding that proof, not the absence of an answer.
