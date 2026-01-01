# Mathias Hauptmann (2016) - P≠NP Proof Attempt

**Attempt ID**: 107 (Woeginger's list)
**Author**: Mathias Hauptmann
**Year**: 2016
**Claim**: P ≠ NP
**Paper**: [On Alternation and the Union Theorem](http://arxiv.org/abs/1602.04781)
**Status**: Not accepted by the complexity theory community

## Summary

In February 2016, Mathias Hauptmann submitted a paper claiming to prove that P is not equal to NP. The proof proceeds by contradiction: Hauptmann assumes P = Σ₂ᵖ (that is, P equals the second level of the polynomial hierarchy), proves a new variant of the Union Theorem of McCreight and Meyer for Σ₂ᵖ, and then derives a contradiction. This would imply that P ≠ Σ₂ᵖ, and consequently P ≠ NP (since P ⊂ NP ⊂ Σ₂ᵖ).

## Main Argument Structure

### Background Concepts

1. **Complexity Classes**:
   - **P**: Problems solvable in deterministic polynomial time
   - **NP**: Problems solvable in nondeterministic polynomial time (or verifiable in deterministic polynomial time)
   - **Σ₂ᵖ**: Second level of polynomial hierarchy, characterized by alternating Turing machines with one existential-universal alternation, or equivalently problems of the form "∃x₁ ∀x₂ M(input, x₁, x₂) = 1" where M runs in polynomial time
   - **DTIME(t(n))**: Problems solvable by deterministic Turing machines in time t(n)

2. **Union Theorem (McCreight-Meyer)**: The original Union Theorem states that for any uniformly computable sequence of time bounds t₁ < t₂ < t₃ < ..., there exists a single time bound t such that:
   ```
   ⋃ᵢ DTIME(tᵢ) = DTIME(t)
   ```
   This means any countable union of deterministic time classes can be captured by a single time bound.

3. **Time Hierarchy Theorem**: For time-constructible functions t, if f(n) = o(t(n)/log t(n)), then:
   ```
   DTIME(f(n)) ⊊ DTIME(t(n))
   ```
   This establishes strict containments between time classes.

### Hauptmann's Approach

**Step 1: Assumption**
Assume P = Σ₂ᵖ (polynomial hierarchy collapses to P)

**Step 2: Union Theorem Variant**
Hauptmann claims to prove a variant of the Union Theorem for Σ₂ᵖ. Specifically, he constructs a union function F with the property that:
- F is computable in F(n)ᶜ time for some constant c
- P = DTIME(F) = Σ₂(F) = Σ₂ᵖ

where Σ₂(F) denotes the second level of the alternating hierarchy with time bound F.

**Step 3: Padding Argument**
Using a padding construction, Hauptmann argues that:
```
DTIME(Fᶜ) = Σ₂(Fᶜ)
```
for some constant c related to the time-constructibility properties of F.

**Step 4: Gupta's Result (claimed)**
Hauptmann invokes a variant of a result attributed to "Gupta" which allegedly shows that for time-constructible functions t:
```
DTIME(t) ⊊ Σ₂(t)
```
That is, there's a strict containment between deterministic and alternating classes at the same time bound.

**Step 5: Contradiction**
Steps 3 and 4 contradict each other: one claims equality (DTIME(Fᶜ) = Σ₂(Fᶜ)) while the other claims strict containment (DTIME(Fᶜ) ⊊ Σ₂(Fᶜ)).

**Conclusion**
The assumption P = Σ₂ᵖ must be false, therefore P ≠ Σ₂ᵖ, which implies P ≠ NP.

## Potential Issues and Gaps

Based on the formalization effort, the following potential issues have been identified:

### 1. **Time-Constructibility Requirements**

The proof critically depends on the function F being time-constructible in a specific sense. The paper may not adequately verify that:
- The constructed function F satisfies the required time-constructibility properties
- The padding argument preserves these properties for Fᶜ
- The conditions for applying "Gupta's result" are met

**Formalization Gap**: When attempting to formalize the time-constructibility requirements, we cannot verify that all necessary conditions hold for the constructed F.

### 2. **The "Gupta's Result" Reference**

The proof relies on a result attributed to someone named "Gupta" about strict separation between DTIME(t) and Σ₂(t). However:
- This result is not clearly cited in the paper
- It's unclear whether such a result exists in the stated generality
- Standard hierarchy theorems for alternating time classes have specific requirements that may not apply here

**Formalization Gap**: We cannot find a formalization or rigorous statement of "Gupta's result" to verify it applies in the claimed context.

### 3. **Union Theorem Extension to Alternating Classes**

The extension of the McCreight-Meyer Union Theorem to alternating complexity classes (specifically Σ₂ᵖ) requires careful handling of:
- The interaction between alternations and time bounds
- Whether the union construction preserves the alternation structure
- The relationship between Σ₂(F) and Σ₂ᵖ under the assumption P = Σ₂ᵖ

**Formalization Gap**: The proof that the union construction works for alternating classes is non-trivial and may contain subtle errors.

### 4. **Padding Argument Details**

The padding argument that derives DTIME(Fᶜ) = Σ₂(Fᶜ) from P = DTIME(F) = Σ₂(F) requires:
- Careful analysis of how problems scale under padding
- Verification that the alternation structure is preserved
- Ensuring the time bounds scale correctly

**Formalization Gap**: The exact details of the padding construction and why it preserves the claimed equalities are unclear.

### 5. **Circular Reasoning Risk**

There's a subtle risk of circular reasoning:
- The assumption P = Σ₂ᵖ is used to construct F with certain properties
- These properties are then used to derive a contradiction
- But the construction of F might already implicitly assume properties that are inconsistent with P = Σ₂ᵖ

**Formalization Gap**: We cannot verify that the construction of F doesn't already presuppose something incompatible with the assumption.

## Reception and Current Status

- **Submission Date**: February 15, 2016 (revised June 3, 2016)
- **Publication Status**: Never accepted to a peer-reviewed venue
- **Community Reception**: The paper received minimal attention from the complexity theory community and was not taken seriously by experts
- **Known Refutation**: No formal published refutation exists, but the lack of acceptance and engagement suggests experts found fatal flaws

The informal consensus appears to be that while the paper is more sophisticated than typical amateur attempts, it contains errors that make the proof invalid. The specific nature of these errors has not been publicly documented in detail.

## Formalization Status

This directory contains formal verification attempts in three proof assistants:
- **Coq** (`coq/Hauptmann2016.v`): Formalization in Coq
- **Lean** (`lean/Hauptmann2016.lean`): Formalization in Lean 4
- **Isabelle** (`isabelle/Hauptmann2016.thy`): Formalization in Isabelle/HOL

The formalization process aims to:
1. Define the relevant complexity classes formally
2. State the assumptions and claimed theorems precisely
3. Attempt to complete the proof
4. Identify where the proof fails or requires unjustified assumptions

## References

1. Mathias Hauptmann (2016). "On Alternation and the Union Theorem". arXiv:1602.04781
2. E. M. McCreight and A. R. Meyer (1969). "Classes of computable functions defined by bounds on computation". STOC '69
3. Gerhard Woeginger's P-versus-NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #107/112)
4. Blog discussion: https://vzn1.wordpress.com/2016/06/20/hauptmann-p%E2%89%A0np-attack-via-polynomial-hierarchy-noncollapse/

## Related Work

- **Polynomial Hierarchy Non-Collapse**: Proving P ≠ NP via showing the polynomial hierarchy doesn't collapse is a known approach, but requires overcoming significant barriers
- **Union Theorems**: Recent work (2021-2024) has refined the McCreight-Meyer Union Theorem with new applications to various complexity classes
- **Alternating Hierarchy**: The relationship between DTIME and alternating classes is well-studied, but exact separations remain open problems

## Lessons for Future Attempts

1. **Time-Constructibility is Delicate**: Proofs involving time-constructible functions require extremely careful verification of constructibility properties
2. **Cite Results Precisely**: Any invocation of "known results" must be cited with precise statements and verified to apply in the claimed context
3. **Union Theorems Have Limits**: The McCreight-Meyer Union Theorem has specific conditions; extending it requires rigorous proof
4. **Hierarchy Theorems Have Gaps**: Known hierarchy theorems don't give separations for all time bounds or all complexity classes
5. **Formalization is Essential**: Formalizing such proofs in proof assistants can catch subtle errors that are easy to miss in informal arguments
