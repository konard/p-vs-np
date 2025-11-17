# Findings: Eli Halylaurin's 2016 P=NP Proof Attempt

## Summary of Formalization

We have formalized Eli Halylaurin's 2016 proof attempt claiming P=NP through the intermediate result PSPACE ⊆ P. The formalization was completed in three proof assistants: Coq, Lean 4, and Isabelle/HOL.

## Main Claim

**Halylaurin's Central Claim**: PSPACE ⊆ P

This claim, if true, would imply:
- P = NP = PSPACE
- Complete collapse of the polynomial hierarchy
- PSPACE-complete problems (like TQBF) would be in P

## Error Analysis

### The Gap in the Proof

The fundamental error in Halylaurin's proof attempt is that **no actual proof is provided** for the claim PSPACE ⊆ P. In our formalization, we represent this gap explicitly using axioms:

- **Coq**: `Axiom Halylaurin_unproven_claim : forall L, in_PSPACE L -> in_P L.`
- **Lean**: `axiom halylaurin_unproven_claim : ∀ L, InPSPACE L → InP L`
- **Isabelle**: `axiomatization where halylaurin_unproven_claim: "InPSPACE problem ⟹ InP problem"`

These axioms represent an **unjustified assumption** rather than a proven theorem.

### Why This Is Problematic

1. **Stronger than P=NP**: The claim PSPACE ⊆ P is actually much stronger than just proving P=NP. It would collapse multiple complexity classes simultaneously.

2. **Contradicts Theoretical Evidence**:
   - PSPACE-complete problems are believed to be strictly harder than NP-complete problems
   - Savitch's theorem shows PSPACE = NPSPACE, so this would imply NPSPACE = P
   - Would collapse the entire polynomial hierarchy to P

3. **No Novel Technique**: The viXra paper provides no indication of:
   - A technique that overcomes known barriers (relativization, natural proofs, algebrization)
   - A polynomial-time algorithm for any PSPACE-complete problem
   - A proof strategy that could plausibly establish such a strong result

4. **Example Consequence - TQBF**: Under this claim, the True Quantified Boolean Formula problem (TQBF), which is PSPACE-complete, would be solvable in polynomial time. This is considered extremely unlikely.

### Standard Complexity Hierarchy

The widely accepted hierarchy is:
```
P ⊊ NP ⊊ PSPACE ⊊ EXPTIME ⊊ NEXPTIME ⊊ ...
```

Halylaurin's claim would collapse this to:
```
P = NP = PSPACE ⊊ EXPTIME ⊊ NEXPTIME ⊊ ...
```

## Formalization Structure

Each of our three formalizations follows the same structure:

1. **Basic Definitions**: Binary strings, decision problems, input size
2. **Polynomial Functions**: Definition of polynomial-time bounds
3. **Turing Machine Model**: Abstract model of computation
4. **Complexity Classes**: Formal definitions of P, NP, and PSPACE
5. **Known Inclusions**: Axiomatized facts (P ⊆ NP, NP ⊆ PSPACE)
6. **Halylaurin's Claim**: The unproven claim PSPACE ⊆ P (as axiom)
7. **Consequences**: Theorems showing P = NP = PSPACE follows from the claim
8. **Error Identification**: Commentary explaining why this is problematic

## Key Theorems Proven

In all three proof systems, we prove:

### Theorem 1: PSPACE ⊆ P implies P = NP
If PSPACE ⊆ P, then every problem in NP is also in P (since NP ⊆ PSPACE ⊆ P).

### Theorem 2: PSPACE ⊆ P implies P = NP = PSPACE
If PSPACE ⊆ P, then all three complexity classes are equal:
- P ⊆ NP (known fact)
- NP ⊆ PSPACE (known fact)
- PSPACE ⊆ P (claimed)
- Therefore: P = NP = PSPACE

These theorems demonstrate the **logical consequences** of Halylaurin's claim, while the axiom representing the claim itself highlights the **absence of proof**.

## Educational Value

This formalization serves as an educational tool demonstrating:

1. **Gap Identification**: How to formally identify gaps in proof attempts
2. **Complexity Class Relationships**: The hierarchy and inclusions between P, NP, and PSPACE
3. **Proof Verification**: The importance of rigorous proof in complexity theory
4. **Critical Analysis**: How to evaluate extraordinary claims in theoretical computer science

## Conclusion

Eli Halylaurin's 2016 proof attempt fails because:
1. No actual proof is provided for the central claim PSPACE ⊆ P
2. The claim contradicts strong theoretical evidence and expert consensus
3. The work lacks peer review and community verification
4. The claim is even stronger than P=NP alone, making it extraordinarily unlikely

The formalization successfully identifies and documents this gap, serving as a case study in formal verification of complexity theory claims and the importance of rigorous proof in theoretical computer science.

## Files

- **README.md**: Detailed description of the attempt and error analysis
- **FINDINGS.md**: This file - summary of formalization findings
- **coq/Halylaurin2016.v**: Coq formalization (247 lines)
- **lean/Halylaurin2016.lean**: Lean 4 formalization (248 lines)
- **isabelle/Halylaurin2016.thy**: Isabelle/HOL formalization (267 lines)

All formalizations compile successfully and demonstrate the same fundamental gap in the proof attempt.
