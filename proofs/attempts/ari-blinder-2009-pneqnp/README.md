# Ari Blinder (2009) - P≠NP Attempt

**Attempt ID**: 58
**Author**: Ari Blinder
**Year**: December 2009
**Claim**: P ≠ NP
**Paper**: "A Possible New Approach to Resolving Open Problems in Computer Science"
**Source**: http://sites.google.com/site/ariblindercswork/
**Listed on**: [Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #58)
**Status**: Retracted by author on March 10, 2010

## Summary

Ari Blinder attempted to prove P ≠ NP in December 2009 by claiming to demonstrate that a language exists within **NP but outside co-NP**, which would establish **NP ≠ co-NP** and consequently imply **P ≠ NP**.

### Main Claim

Blinder's approach centered on proving:
1. There exists a language **L ∈ NP \ co-NP** (in NP but not in co-NP)
2. If NP ≠ co-NP, then P ≠ NP (since P is closed under complement)
3. Therefore, P ≠ NP

### Author's Retraction

On **March 10, 2010**, Ari Blinder publicly announced that he had **identified a flaw in his proof**, invalidating the claimed result. The proof was withdrawn by the author.

## The Argument

### Core Approach

Blinder's strategy relied on the known relationship between complexity classes:

1. **P is closed under complement**: If L ∈ P, then L̄ (complement) ∈ P
2. **Co-NP definition**: co-NP = {L̄ | L ∈ NP}
3. **Known relationship**: P ⊆ NP ∩ co-NP
4. **Key insight**: If NP ≠ co-NP, then NP ∩ co-NP ≠ NP
5. **Attempted conclusion**: Since P ⊆ NP ∩ co-NP, if NP ≠ co-NP, then P ≠ NP

### The Strategy

To prove P ≠ NP, Blinder attempted to:
1. **Construct** or **identify** a specific language L
2. **Prove** that L ∈ NP (has polynomial-time verification)
3. **Prove** that L̄ ∉ NP (complement cannot be verified in polynomial time)
4. **Conclude** NP ≠ co-NP
5. **Therefore** P ≠ NP

This approach is theoretically sound IF one can rigorously prove the existence of such a language. However, proving NP ≠ co-NP is considered almost as hard as proving P ≠ NP itself.

## The Error

### Author-Identified Flaw

Blinder himself discovered and announced a critical flaw in the proof on March 10, 2010. While the specific technical error is not publicly documented in detail, common issues with this type of approach include:

### 1. **Difficulty in Proving L̄ ∉ NP**

The core challenge in separating NP from co-NP is rigorously proving that the complement of a language is NOT in NP. This requires showing:
- There is no polynomial-time verifier for L̄
- This is a universal negative claim (proving non-existence)
- Such proofs typically require techniques that also work for P ≠ NP

### 2. **Circular Reasoning Risk**

Many attempts to prove NP ≠ co-NP fall into circular reasoning:
- Assuming properties of L that implicitly require NP ≠ co-NP
- Using complexity-theoretic assumptions equivalent to the conclusion
- Not establishing the required properties from first principles

### 3. **Known Barriers Apply**

Proving NP ≠ co-NP faces similar barriers to proving P ≠ NP:

**Relativization Barrier**:
- Baker-Gill-Solovay (1975) showed there exist oracles A and B where:
  - P^A = NP^A (P equals NP relative to A)
  - P^B ≠ NP^B (P differs from NP relative to B)
- Similarly, NP ≠ co-NP can relativize in both directions
- Proofs using only relativizing techniques cannot resolve these questions

**Natural Proofs Barrier**:
- Razborov-Rudich (1997) showed limitations on certain proof techniques
- "Natural" properties (constructive, widely applicable, useful) cannot prove circuit lower bounds unless strong cryptographic assumptions fail
- This barrier also applies to separating NP from co-NP

### 4. **Insufficient Formalization**

Without access to the full proof details, likely issues include:
- Incomplete formal proof of L ∈ NP \ co-NP
- Gap in the argument where a critical property is assumed
- Missing rigorous complexity-theoretic justification
- Potential confusion between intuitive arguments and formal proofs

### 5. **Why NP ≠ co-NP is Nearly as Hard as P ≠ NP**

The relationship between these problems:
- **Known**: P = co-P (P is closed under complement)
- **Known**: P ⊆ NP ∩ co-NP
- **Unknown**: Is P = NP ∩ co-NP?
- **Unknown**: Is NP = co-NP?

If NP ≠ co-NP, then P ≠ NP (contrapositive: if P = NP, then NP = co-NP).
But proving NP ≠ co-NP requires overcoming essentially the same barriers as P ≠ NP.

## Formalization Approach

Our formalization demonstrates:

1. **The structure of the argument**: Formalizes the logical relationship between NP ≠ co-NP and P ≠ NP
2. **Where the gap occurs**: Shows that proving L ∈ NP \ co-NP requires assumptions equivalent to the conclusion
3. **Why the barriers apply**: Demonstrates how relativization and natural proofs affect this approach
4. **The retraction lesson**: Highlights the importance of peer review and self-criticism in mathematical research

### Educational Value

This attempt provides important lessons:
- **Self-correction**: Blinder's retraction demonstrates scientific integrity
- **Difficulty of separation**: Shows why separating complexity classes is hard
- **Barrier awareness**: Illustrates why known barriers must be addressed
- **Rigor requirement**: Emphasizes need for complete formal proofs

## Formalization Status

### Coq (`coq/BlinderAttempt.v`)
- Models P, NP, and co-NP complexity classes
- Formalizes the relationship: (NP ≠ co-NP) → (P ≠ NP)
- **Identifies the gap**: Cannot prove existence of L ∈ NP \ co-NP without circular reasoning
- Demonstrates relativization barrier with oracle constructions

### Lean (`lean/BlinderAttempt.lean`)
- Provides formal definitions of P, NP, co-NP
- Shows the logical structure of Blinder's approach
- **Identifies the gap**: Proving L̄ ∉ NP requires proving a universal negative
- Marks where additional (unprovable) assumptions would be needed

### Isabelle (`isabelle/BlinderAttempt.thy`)
- Structured representation of the separation argument
- Formalizes complement closure and class relationships
- **Identifies the gap**: The core claim (NP ≠ co-NP) remains unproven
- Shows where the known barriers prevent progress

## Conclusion

Blinder's attempt is **not a valid proof** of P ≠ NP because:

1. ❌ Contains a critical flaw (identified by author)
2. ❌ Proving NP ≠ co-NP is nearly as hard as proving P ≠ NP
3. ❌ Subject to the same proof barriers (relativization, natural proofs)
4. ❌ Would require techniques that overcome fundamental obstacles
5. ✅ **Author retracted the proof** after finding the error (demonstrates scientific integrity)

### What This Shows

This formalization demonstrates important principles:

1. **Self-correction in science**: Blinder's willingness to retract shows proper scientific practice
2. **Difficulty of complexity separation**: Separating NP from co-NP faces similar obstacles to P vs NP
3. **Barrier awareness**: Valid approaches must address or circumvent known proof barriers
4. **Need for rigor**: Intuitive arguments must be backed by complete formal proofs
5. **Value of peer review**: Mathematical claims require scrutiny and verification

### Positive Aspects

Despite the flaw, this attempt demonstrates:
- ✅ Understanding of the relationship between P, NP, and co-NP
- ✅ A theoretically valid proof strategy (if NP ≠ co-NP could be proven)
- ✅ Scientific integrity in retracting flawed work
- ✅ Contribution to understanding what doesn't work

## References

1. Blinder, A. (2009). "A Possible New Approach to Resolving Open Problems in Computer Science" (Retracted)
2. Woeginger, G. J. "The P-versus-NP page", https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P=?NP Question", SIAM Journal on Computing
4. Razborov, A., Rudich, S. (1997). "Natural Proofs", Journal of Computer Science and System Sciences
5. Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach", Cambridge University Press

## Related Work

- [proofs/p_not_equal_np/](../../p_not_equal_np/README.md) - Framework for verifying P ≠ NP proof attempts
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](../../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of valid approaches
- [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md) - Tools for formal verification

## Notes on Complexity Class Relationships

### Known Facts
- P = co-P (P is closed under complement)
- P ⊆ NP ∩ co-NP
- If P = NP, then NP = co-NP

### Open Questions
- Is P = NP ∩ co-NP?
- Is NP = co-NP?
- What is the structure of NP ∩ co-NP?

### Implications
- NP ≠ co-NP ⟹ P ≠ NP (contrapositive of P = NP ⟹ NP = co-NP)
- But proving NP ≠ co-NP is considered extremely difficult
- No known techniques can prove this without also proving P ≠ NP
