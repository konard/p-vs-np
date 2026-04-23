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

## The Error in the Proof

Through formal verification in Rocq and Lean, the **critical flaw** in Hauptmann's proof has been identified: the claimed contradiction between two properties of the union function is **not actually a contradiction**. The proof by contradiction therefore fails.

### The Claimed Contradiction

Hauptmann claims that under the assumption P = Σ₂ᵖ, the union function F must satisfy two incompatible bounds:

- **Self-referential bound**: F(n) ≤ F(n)^c for some constant c
- **Polynomial bound**: F(n) ≤ n^(k+1) for some constant k

### Why This Is Not a Contradiction

Both bounds can hold simultaneously. For example, let F(n) = n with c = 1 and k = 1:
- F(n) ≤ F(n)^c becomes n ≤ n¹ ✓
- F(n) ≤ n^(k+1) becomes n ≤ n² ✓

The self-referential bound F(n) ≤ F(n)^c is trivially satisfied for c ≥ 1 and any positive F(n). It places no real constraint on F. The formalizations (Rocq, Lean) demonstrate this by exhibiting explicit functions satisfying both bounds without contradiction.

### Additional Gaps

1. **Insufficient for P ≠ NP**: Even if P ≠ Σ₂ᵖ were established, this alone would not imply P ≠ NP. Since P ⊆ NP ⊆ Σ₂ᵖ, we could still have P = NP ⊊ Σ₂ᵖ. No additional argument bridges this gap.

2. **Unclear "Gupta's Result" reference**: The proof invokes a result attributed to "Gupta" about strict separation between DTIME(t) and Σ₂(t), but this result is not clearly cited or verified to apply in the claimed context.

3. **Union Theorem extension to alternating classes**: The extension of the McCreight-Meyer Union Theorem to Σ₂ᵖ requires careful verification of how alternations interact with the union construction. The paper does not provide sufficient justification.

4. **Padding argument details**: The padding construction that derives DTIME(Fᶜ) = Σ₂(Fᶜ) from P = DTIME(F) = Σ₂(F) is not fully justified in the paper.

For the complete formal analysis, see [ERROR_ANALYSIS.md](./ERROR_ANALYSIS.md).

## Reception and Current Status

- **Submission Date**: February 15, 2016 (revised June 3, 2016)
- **Publication Status**: Never accepted to a peer-reviewed venue
- **Community Reception**: The paper received minimal attention from the complexity theory community and was not taken seriously by experts
- **Known Refutation**: No formal published refutation exists, but the lack of acceptance and engagement suggests experts found fatal flaws

The informal consensus appears to be that while the paper is more sophisticated than typical amateur attempts, it contains errors that make the proof invalid. The specific nature of these errors has not been publicly documented in detail.

## Formalization Status

This directory contains formal verification attempts in two proof assistants:
- **Rocq** (`rocq/Hauptmann2016.v`): Formalization in Rocq — identifies non-contradiction of the claimed bounds
- **Lean** (`lean/Hauptmann2016.lean`): Formalization in Lean 4 — identifies non-contradiction of the claimed bounds

Both formalizations independently demonstrate the `Hauptmann_No_Contradiction` theorem showing that the two bounds on F can hold simultaneously.

## File Structure

```
proofs/attempts/mathias-hauptmann-2016-pneqnp/
├── README.md                       # This file
├── ERROR_ANALYSIS.md               # Detailed error analysis
├── paper/
│   └── hauptmann-2016.pdf          # Original paper (arXiv:1602.04781)
├── rocq/
│   └── Hauptmann2016.v             # Rocq formalization
└── lean/
    └── Hauptmann2016.lean          # Lean 4 formalization
```

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
