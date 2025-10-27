# Eli Halylaurin (2016) - P=NP Attempt

**Attempt ID**: 110
**Author**: Eli Halylaurin
**Year**: 2016
**Claim**: P=NP
**Paper**: "An Attempt to Demonstrate P=NP"
**Source**: http://vixra.org/abs/1605.0278
**Listed in**: Woeginger's P versus NP page (Entry #110)

## Summary

In summer 2016, Eli Halylaurin claimed to prove P=NP by showing that PSPACE ⊆ P. The argument relies on the well-known complexity class inclusions:

```
P ⊆ NP ⊆ PSPACE
```

If PSPACE ⊆ P were true, this would indeed imply:
- PSPACE ⊆ P
- P ⊆ NP ⊆ PSPACE ⊆ P

Therefore: P = NP = PSPACE (all three classes would collapse)

## The Main Argument

The proof attempt claims to demonstrate that **PSPACE ⊆ P**, which would have profound implications:

1. Since we know P ⊆ NP (by definition)
2. And we know NP ⊆ PSPACE (by Savitch's theorem)
3. If PSPACE ⊆ P, then we get: P ⊆ NP ⊆ PSPACE ⊆ P
4. Therefore, P = NP = PSPACE

## Known Complexity Theory Facts

### What We Know is True:
- **P ⊆ NP**: Every problem solvable in polynomial time is verifiable in polynomial time
- **NP ⊆ PSPACE**: Every NP problem can be solved in polynomial space (by trying all possibilities)
- **PSPACE ⊆ EXPTIME**: Problems solvable in polynomial space can be solved in exponential time
- **P ⊆ PSPACE**: Polynomial time implies polynomial space (you can't use more space than time steps)

### What We Strongly Believe (but haven't proven):
- **P ≠ NP**: Most complexity theorists believe this
- **NP ≠ PSPACE**: Strongly believed but unproven
- **PSPACE ≠ EXPTIME**: By time hierarchy, we know PSPACE ⊊ EXPSPACE, but PSPACE vs EXPTIME is open

### Separations We Have Proven:
- **P ⊊ EXPTIME**: By time hierarchy theorem (proven by Hartmanis and Stearns, 1965)
- **NP ⊊ NEXPTIME**: By nondeterministic time hierarchy
- **PSPACE ⊊ EXPSPACE**: By space hierarchy theorem

## The Critical Error

The claim that **PSPACE ⊆ P** is **almost certainly false** and contradicts well-established complexity theory results. Here's why:

### Problem 1: Time Hierarchy Theorem
We know from the **Time Hierarchy Theorem** that:
```
P ⊊ EXPTIME
```

This is a **proven theorem**, not a conjecture. If PSPACE ⊆ P were true, combined with PSPACE ⊆ EXPTIME, we would have:
```
PSPACE ⊆ P ⊊ EXPTIME
```

However, this creates problems because:
- We know PSPACE contains problems that are PSPACE-complete (like TQBF - True Quantified Boolean Formula)
- TQBF is believed to require exponential time
- If PSPACE ⊆ P, then TQBF ∈ P, which would be a stunning result contradicting extensive research

### Problem 2: PSPACE-Complete Problems
There are known **PSPACE-complete** problems, such as:
- **TQBF** (True Quantified Boolean Formula)
- **Generalized Geography**
- **Chess on an n×n board**
- **Go on an n×n board**

These problems are complete for PSPACE, meaning:
1. They are in PSPACE
2. Every problem in PSPACE reduces to them in polynomial time

If PSPACE ⊆ P, then all these PSPACE-complete problems would be in P. This would mean:
- We could solve TQBF in polynomial time
- We could solve n×n Chess optimally in polynomial time
- We could solve n×n Go optimally in polynomial time

This is considered **extremely unlikely** by the complexity theory community.

### Problem 3: The Proof Burden
To prove PSPACE ⊆ P, one would need to show that **every** problem solvable in polynomial space can be solved in polynomial time. This is an extraordinarily strong claim that would require:

1. **A polynomial-time algorithm** for a PSPACE-complete problem (like TQBF), OR
2. **A proof** that polynomial space can always be simulated in polynomial time

Neither has been achieved, and extensive research suggests this is false.

### Problem 4: Quantifier Alternation
PSPACE-complete problems like TQBF involve **alternating quantifiers**:
```
∃x₁ ∀x₂ ∃x₃ ∀x₄ ... φ(x₁, x₂, x₃, x₄, ...)
```

The alternation of ∃ (existential) and ∀ (universal) quantifiers creates a fundamental computational difficulty. Polynomial time algorithms struggle with this kind of alternation because:
- Each ∀ quantifier requires checking all possibilities
- The depth of quantifier alternation grows with input size
- No polynomial-time algorithm is known for handling arbitrary quantifier alternation

## Formalization Strategy

Our formalization will:

1. **Define the complexity classes**: P, NP, PSPACE
2. **State the known inclusions**: P ⊆ NP ⊆ PSPACE
3. **Assume PSPACE ⊆ P**: This is Halylaurin's claim
4. **Derive the consequences**: P = NP = PSPACE
5. **Identify where the proof fails**: The assumption PSPACE ⊆ P is unjustified

The formalization will show that:
- The logical structure is valid (if PSPACE ⊆ P, then P = NP = PSPACE)
- But the critical assumption (PSPACE ⊆ P) is unproven and likely false
- The error is in **assuming** rather than **proving** PSPACE ⊆ P

## The Gap in the Proof

The fundamental gap is:

> **The proof assumes PSPACE ⊆ P without justification.**

This is not a minor technical error but a complete absence of proof for the central claim. The paper would need to:

1. Provide a polynomial-time algorithm for a PSPACE-complete problem, OR
2. Prove that polynomial space simulation requires only polynomial time, OR
3. Show some other fundamental reason why PSPACE ⊆ P

None of these is provided in a valid form.

## Educational Value

This attempt demonstrates:

1. **Valid logical reasoning from false premises**: The implication chain is correct, but the foundation is false
2. **The importance of proof vs. assumption**: Stating "PSPACE ⊆ P" doesn't make it true
3. **Understanding complexity class separations**: Why we believe these classes are distinct
4. **The role of complete problems**: PSPACE-complete problems characterize the difficulty of the entire class

## Formalization Files

- `coq/EliHalylaurin2016.v` - Coq formalization showing the logical structure and where the proof fails
- `lean/EliHalylaurin2016.lean` - Lean formalization with detailed error analysis
- `isabelle/EliHalylaurin2016.thy` - Isabelle/HOL formalization of the attempt

Each formalization:
- Defines P, NP, and PSPACE
- Shows the known inclusions
- Demonstrates that PSPACE ⊆ P would imply P = NP = PSPACE
- Marks the unjustified assumption with `sorry`/`Admitted`/`oops`
- Documents why this assumption is problematic

## Conclusion

The Halylaurin attempt is **invalid** because it assumes its conclusion without proof. The claim PSPACE ⊆ P is:
- Unproven
- Contradicts established beliefs in complexity theory
- Would require extraordinary evidence
- Is the central claim that needed proof, not an axiom to assume

This is a common pattern in failed P vs NP attempts: **assuming the result** rather than proving it.

## References

- Woeginger, G. J. "The P-versus-NP page" - Entry #110
- Savitch, W. J. (1970). "Relationships between nondeterministic and deterministic tape complexities"
- Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms"
- Papadimitriou, C. H. (1994). "Computational Complexity" - Chapter on PSPACE
