# Formalization: N.C.A. da Costa & F.A. Doria (2003) - P vs NP Unprovability Claim

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 9
- **Authors**: Newton C.A. da Costa & Francisco A. Doria
- **Year**: 2003 (with addendum in 2006)
- **Claim**: P vs NP is **unprovable in ZFC** (independence claim)
- **Status**: **REFUTED** - Contains fundamental logical errors and gaps
- **Source**: [Woeginger's P vs NP Attempts List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #9)
- **Paper**: "Consequences of an exotic definition for P=NP", Applied Mathematics and Computation 145 (2003), pp. 655-665

## The Argument

Da Costa and Doria's 2003 paper attempts to prove that the statement "P ≠ NP" is unprovable in ZFC (Zermelo-Fraenkel set theory with the axiom of choice). Their approach involves:

1. **Defining an exotic variant** [P = NP]' that differs from the standard P = NP formulation
2. **Showing** that [P = NP]' is not refutable in ZFC (by construction, it includes a disjunct that cannot be refuted)
3. **Claiming** that this proves ZFC + [P = NP] is consistent (Corollary 4.6)
4. **Concluding** that P ≠ NP cannot be proven in ZFC

Their main technical claim (Corollary 4.6) states:
> "If ZFC is consistent, then it remains so when P=NP is added as an additional axiom."

The 2006 addendum reformulates this as:
> "If ZFC + [P = NP]' is ω-consistent, then ZFC + [P = NP] is consistent."

## The Errors

This argument contains **multiple fundamental logical and technical errors** identified by expert reviewers:

### 1. **Critical Gap in the Main Proof** (Andreas Blass)

**The Flaw**: The proof of Corollary 4.6 contains a critical error.

**Expert Review**: Andreas Blass, in his Mathematical Reviews review MR2009291 (2004f:03076), writes:

> "The authors claim to prove (Corollary 4.6) that, if ZFC is consistent, then it remains so when P=NP is added as an additional axiom. Unfortunately, there is an error in the proof [...]."

Blass further notes:
> "The absence of rigor led to numerous errors (and ambiguities)."

**Why It's Wrong**:
- The step from [P = NP]' to P = NP is not justified
- The exotic formulation [P = NP]' differs from standard P = NP in critical ways
- The consistency of ZFC + [P = NP]' does not imply consistency of ZFC + [P = NP]

### 2. **Insufficient Justification** (Ralf Schindler)

**The Flaw**: The transition from the exotic definition to the standard formulation is too brief and contains a gap.

**Expert Review**: German logician Ralf Schindler reviewed the proof and identified that:
> "This last step is too short and contains a gap."

**Why It's Wrong**:
- The key step connecting [P = NP]' to P = NP lacks rigorous justification
- The construction deliberately makes [P = NP]' non-refutable, but this doesn't transfer to P = NP
- The gap is precisely where the independence claim would need to be established

### 3. **Missing ω-Consistency Proof**

**The Flaw**: The 2006 reformulation depends on proving ZFC + [P = NP]' is ω-consistent, but no such proof is provided.

**Why It's Wrong**:
- The authors claim: "If ZFC + [P = NP]' is ω-consistent, then ZFC + [P = NP] is consistent"
- But they never establish that ZFC + [P = NP]' is ω-consistent
- Without this, the conditional statement is useless for proving independence

**What Would Be Needed**:
- A formal proof that ZFC + [P = NP]' is ω-consistent
- This has not been provided in either the 2003 paper or the 2006 addendum

### 4. **Confusion Between Standard and Exotic Formulations**

**The Flaw**: The paper conflates properties of the exotic definition [P = NP]' with the standard P = NP.

**Why It's Wrong**:
- [P = NP]' is constructed to be non-refutable by design (contains an irrefutable disjunct)
- This construction says nothing about whether standard P = NP is refutable
- The two formulations coincide in the standard model but differ metamathematically
- Properties that hold for [P = NP]' (non-refutability) don't automatically transfer to P = NP

### 5. **Methodological Issues with Exotic Definitions**

**The Flaw**: Using exotic definitions to prove independence claims is inherently problematic.

**Why It's Wrong**:
- Any statement can be reformulated with an added irrefutable disjunct
- For example, define [Goldbach]' = "Goldbach's conjecture OR [some irrefutable statement]"
- Then [Goldbach]' is non-refutable by construction
- But this tells us nothing about whether Goldbach's conjecture itself is independent of ZFC
- The exotic formulation merely "hides" a tautology in the definition

**Example**:
```
Let S be any mathematical statement
Define S' = "S OR (Con(ZFC))" where Con(ZFC) = "ZFC is consistent"
Then S' is not refutable in ZFC (assuming ZFC is consistent)
But this doesn't prove S is independent of ZFC!
```

### 6. **Lack of Formal Rigor**

**The Flaw**: The paper lacks the formal rigor expected for independence results in mathematical logic.

**Why It's Wrong**:
- Independence results require:
  - Precise formal definitions
  - Construction of models where statements have different truth values
  - Rigorous proof that these models satisfy ZFC axioms
- Da Costa & Doria's paper provides insufficient detail for verification
- Multiple expert reviewers noted the absence of rigor

**Comparison with Valid Independence Proofs**:
- Cohen's independence of CH: Constructed explicit forcing models
- Gödel's consistency of CH: Built constructible universe L
- Da Costa & Doria: Rely on an exotic definition trick without model construction

## What Would Be Required for a Valid Independence Proof

To validly prove P vs NP is independent of ZFC, one would need:

### For Consistency of ZFC + [P ≠ NP]:
1. **Construct a model** M₁ of ZFC where P ≠ NP holds
2. **Verify** that M₁ satisfies all ZFC axioms
3. **Verify** that in M₁, there exists a problem in NP but not in P

### For Consistency of ZFC + [P = NP]:
1. **Construct a model** M₂ of ZFC where P = NP holds
2. **Verify** that M₂ satisfies all ZFC axioms
3. **Verify** that in M₂, every problem in NP is also in P

### Key Challenges:
- **Definability**: P and NP must be properly defined in the model theory of ZFC
- **Absoluteness**: Many complexity-theoretic notions are absolute across models
- **Natural Problems**: The definitions must capture what we mean by P and NP, not just formal variants

**What Da Costa & Doria Didn't Do**:
- They didn't construct explicit models
- They didn't verify ZFC axioms hold in constructed models
- They relied on a definitional trick rather than model-theoretic methods

## Formal Verification

This directory contains formalizations in three proof assistants that expose these errors:

### Implementations

1. **[Rocq](rocq/DaCostaDoriaAttempt.v)** - Rocq formalization showing the gaps in the argument
2. **[Lean 4](lean/DaCostaDoriaAttempt.lean)** - Lean formalization with detailed error analysis
3. **[Isabelle/HOL](isabelle/DaCostaDoriaAttempt.thy)** - Isabelle formalization demonstrating the missing steps

### What the Formalizations Show

Each formalization:
- ✅ Defines the structure of the attempted proof
- ✅ Distinguishes between exotic [P = NP]' and standard P = NP
- ✅ Identifies the critical gap in Corollary 4.6
- ✅ Shows that non-refutability of [P = NP]' doesn't imply independence of P = NP
- ✅ Demonstrates that the proof requires unproven assumptions
- ✅ Makes explicit what would be needed for a valid independence proof

## Key Insights

This attempt illustrates several important points about independence proofs:

### 1. **Definitional Tricks Don't Prove Independence**
- Adding irrefutable disjuncts to definitions doesn't establish independence
- True independence requires model construction and verification

### 2. **The Bar for Independence Proofs is High**
- Independence results in set theory (like Cohen's forcing) require:
  - Explicit model construction
  - Detailed verification of axioms
  - Proof that models differ on the statement in question
- Informal arguments and exotic definitions are insufficient

### 3. **Expert Review is Essential**
- Da Costa & Doria's work was published in Applied Mathematics and Computation
- It was subsequently reviewed by experts in mathematical logic (Blass, Schindler)
- These reviews identified fundamental gaps that invalidate the main claims
- This demonstrates the importance of peer review by domain experts

### 4. **P vs NP Independence Remains Open**
- Despite this flawed attempt, whether P vs NP is independent of ZFC remains unknown
- Some complexity theorists believe it's unlikely to be independent
- Others think independence is possible but would require fundamentally new techniques
- See Scott Aaronson's "Is P vs NP Formally Independent?" for discussion

## Why This is Educationally Valuable

Despite being incorrect, formalizing this attempt provides important lessons:

1. **Methodological Rigor**: Shows why formal rigor matters in mathematical logic
2. **Common Mistakes**: Illustrates pitfalls in attempting independence proofs
3. **Expert Review**: Demonstrates the value of domain-expert peer review
4. **Formalization Benefits**: The errors become clearer when we attempt to formalize the argument
5. **Model Theory**: Highlights the importance of proper model-theoretic techniques

## Complexity-Theoretic Context

### Why P vs NP Independence is Considered Unlikely (by some experts)

1. **Natural Statements**: P vs NP is a "natural" mathematical statement about algorithms
2. **Absoluteness**: Many complexity-theoretic notions are absolute across set-theoretic models
3. **Concrete Character**: Unlike set-theoretic statements (CH, large cardinals), P vs NP asks about specific computational problems
4. **Consensus**: While not proven, many complexity theorists expect P ≠ NP to be provable (or refutable) in ZFC

### Known Barriers to P ≠ NP Proofs

A valid proof of P ≠ NP must overcome:
- **Relativization** (Baker-Gill-Solovay, 1975)
- **Natural Proofs** (Razborov-Rudich, 1997)
- **Algebrization** (Aaronson-Wigderson, 2008)

Da Costa & Doria's approach doesn't engage with these barriers, as it attempts to prove unprovability rather than P ≠ NP itself.

## References

### Primary Sources
- **Da Costa, N.C.A., Doria, F.A.** (2003). "Consequences of an exotic definition for P=NP." *Applied Mathematics and Computation* 145, pp. 655-665.
- **Da Costa, N.C.A., Doria, F.A.** (2006). "Addendum to 'Consequences of an exotic formulation for P=NP'." *Applied Mathematics and Computation* 172, pp. 1364-1367.

### Expert Reviews
- **Blass, A.** (2004). Review MR2009291 (2004f:03076). *Mathematical Reviews (MathSciNet)*.
- **Schindler, R.** Review available at: http://wwwmath.uni-muenster.de/math/inst/logik/org/staff/rds/review.ps

### Woeginger's List
- **Woeginger, G. J.** "The P-versus-NP page" (Entry #9)
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Background on Independence Results
- **Cohen, P.** (1963). "The independence of the continuum hypothesis." *PNAS* 50(6), 1143-1148.
- **Gödel, K.** (1940). *The Consistency of the Continuum Hypothesis*. Princeton University Press.
- **Kunen, K.** (2011). *Set Theory*. College Publications. (Chapter on forcing)

### P vs NP Independence Discussion
- **Aaronson, S.** (2011). "Is P vs. NP formally independent?" Blog post.
  - https://scottaaronson.blog/?p=1948
- **Aaronson, S.** (2013). "P/NP, and why we believe things."
  - https://www.scottaaronson.com/papers/indep.pdf
- **Ben-David, S., Turing Centenary Workshop.** (2012). "Can the P vs NP question be independent of the axioms?"

### Complexity Theory Background
- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.
- **Sipser, M.** (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.

## Verification Status

- ✅ **Rocq**: Formalization complete - Shows gaps and invalid steps
- ✅ **Lean 4**: Formalization complete - Identifies missing proofs
- ✅ **Isabelle/HOL**: Formalization complete - Demonstrates incompleteness

## How to Verify

### Rocq
```bash
cd rocq
rocq compile DaCostaDoriaAttempt.v
```

### Lean 4
```bash
cd lean
lake build
```

### Isabelle/HOL
```bash
isabelle build -D isabelle
```

## Related Work in This Repository

### Similar Attempts at Independence
- See other attempts on Woeginger's list that claim unprovability or independence

### Barriers Literature
- Documentation on relativization, natural proofs, and algebrization barriers
- These are the obstacles any valid P ≠ NP proof must overcome

## License

This formalization is provided for educational purposes. See repository [LICENSE](../../../LICENSE).

---

**Part of**: [Issue #433](https://github.com/konard/p-vs-np/issues/433) | **Parent Issue**: [#44 - Test all P vs NP attempts formally](https://github.com/konard/p-vs-np/issues/44)
