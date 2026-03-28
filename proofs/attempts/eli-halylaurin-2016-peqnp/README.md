# Eli Halylaurin (2016) - P=NP Attempt

**Attempt ID**: 110 (from Woeginger's list)
**Author**: Eli Halylaurin
**Year**: 2016
**Claim**: P = NP
**Source**: viXra:1605.0278 - "An Attempt to Demonstrate P=NP"
**Reference**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #110)

## Summary

In summer 2016, Eli Halylaurin published a paper claiming to prove P=NP on viXra.org. The central claim of the proof is that **PSPACE ⊆ P**. Given the known inclusions P ⊆ NP ⊆ PSPACE, the author argues that showing PSPACE ⊆ P would complete the cycle and establish P = NP.

## Main Argument

The proof structure follows this logical chain:

1. **Known fact**: P ⊆ NP (every polynomial-time decidable problem is also in NP)
2. **Known fact**: NP ⊆ PSPACE (every NP problem can be solved using polynomial space)
3. **Claimed result**: PSPACE ⊆ P (all polynomial-space problems can be solved in polynomial time)
4. **Conclusion**: P ⊆ NP ⊆ PSPACE ⊆ P, therefore P = NP = PSPACE

The key claim is step 3: that PSPACE ⊆ P.

## The Error

This proof attempt contains a fundamental error that makes the claim extremely unlikely to be correct:

### 1. The Claim is Stronger Than P=NP

The claim that **PSPACE ⊆ P** is actually a much stronger claim than P=NP alone. This would imply:
- P = NP = PSPACE
- All three complexity classes collapse into one
- Problems like TQBF (True Quantified Boolean Formula), which is PSPACE-complete, would be solvable in polynomial time

### 2. Contradicts Strong Theoretical Evidence

There is overwhelming theoretical evidence that PSPACE is strictly larger than P:

- **PSPACE-complete problems** include quantified Boolean formulas, games like generalized chess and Go, and many other problems that are believed to be fundamentally harder than NP-complete problems
- **Savitch's Theorem** shows that PSPACE = NPSPACE, so claiming PSPACE ⊆ P would also imply NPSPACE = P
- The **polynomial hierarchy** would collapse completely if PSPACE = P
- Many complexity theorists believe P ≠ NP ⊊ PSPACE, making PSPACE ⊆ P extremely unlikely

### 3. No Credible Proof Technique

The paper was published on viXra (a non-peer-reviewed preprint server) and has not been verified by the complexity theory community. A proof of PSPACE ⊆ P would be even more groundbreaking than a proof of P=NP, as it would:
- Solve P vs NP as a corollary
- Solve P vs PSPACE
- Collapse the entire polynomial hierarchy
- Represent one of the most dramatic results in all of theoretical computer science

Such an extraordinary claim would require extraordinary evidence and novel techniques that overcome known barriers (relativization, natural proofs, algebrization). The viXra paper provides no indication of such breakthrough techniques.

### 4. Standard Hierarchy Belief

The standard complexity theory hierarchy is believed to be:
```
P ⊊ NP ⊊ PSPACE ⊊ EXPTIME ⊊ NEXPTIME ⊊ ...
```

Proving PSPACE ⊆ P would contradict this entire hierarchy and collapse it to just:
```
P = NP = PSPACE ⊊ EXPTIME ⊊ ...
```

This is considered extraordinarily unlikely by the theoretical computer science community.

## Formalization Approach

In this formalization, we:

1. **Define PSPACE** as the class of decision problems solvable by a Turing machine using polynomial space
2. **State the claim** that PSPACE ⊆ P
3. **Show the logical consequence** that if PSPACE ⊆ P, then P = NP = PSPACE
4. **Identify the gap**: The formalization makes it clear that this is an unproven claim that lacks justification

The formalization helps demonstrate:
- What would need to be proven (a polynomial-time algorithm for every PSPACE problem)
- Why this is such a strong claim
- That no such proof is provided in the original work

## Known Facts Used

The formalization relies on these established results:
- **P ⊆ NP**: Trivial (a polynomial-time decider is a polynomial-time verifier)
- **NP ⊆ PSPACE**: Known theorem (nondeterministic polynomial time can be simulated in polynomial space)
- **PSPACE ⊆ EXPTIME**: Follows from the fact that polynomial space allows at most exponentially many configurations

## Conclusion

This proof attempt fails because:
1. It makes an extraordinary claim (PSPACE ⊆ P) without providing a valid proof
2. The claim contradicts strong theoretical evidence and expert consensus
3. No novel technique is presented that would overcome known barriers to such a proof
4. The work was not peer-reviewed and has not been accepted by the complexity theory community

The formalization serves as an educational tool to understand:
- The relationship between P, NP, and PSPACE
- Why PSPACE ⊆ P would be even stronger than P=NP
- The importance of rigorous proof in complexity theory
- How to identify gaps in claimed proofs

## Files

- `rocq/Halylaurin2016.v` - Rocq formalization
- `lean/Halylaurin2016.lean` - Lean 4 formalization
- `isabelle/Halylaurin2016.thy` - Isabelle/HOL formalization

Each formalization:
1. Defines the complexity classes P, NP, and PSPACE
2. States the known inclusions
3. Shows what the claim PSPACE ⊆ P would imply
4. Identifies the unproven assumption (using axioms to mark the gap)

## References

- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- viXra paper: http://vixra.org/abs/1605.0278
- Arora & Barak, "Computational Complexity: A Modern Approach" (2009) - Chapters on space complexity
- Sipser, "Introduction to the Theory of Computation" - PSPACE and complexity hierarchies
