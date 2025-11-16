# Arto Annila (2009) - P≠NP Attempt

**Attempt ID**: 50
**Author**: Arto Annila
**Year**: 2009 (published 2012)
**Claim**: P ≠ NP
**Paper**: "Physical portrayal of computational complexity"
**Source**: [arXiv:0906.1084](https://arxiv.org/abs/0906.1084), ISRN Computational Mathematics, 2012, ID: 321372, pp. 1-15
**Listed on**: [Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #50)

## Summary

Arto Annila attempts to prove P ≠ NP by using a **thermodynamic and physical entropy perspective** on computational complexity. The author argues that computational processes can be understood through the lens of thermodynamic state space evolution and dissipative transformations.

### Main Claim

> "The state space of a non-deterministic finite automaton is evolving due to the computation itself hence it cannot be efficiently contracted using a deterministic finite automaton that will arrive at a solution in super-polynomial time. The solution of the NP problem itself is verifiable in polynomial time (P) because the corresponding state is stationary."

In other words, Annila claims that:
1. NP problems have **dynamically evolving state spaces** during computation
2. P algorithms can **efficiently contract** to solutions via deterministic sequences
3. This fundamental difference in state space behavior implies P ≠ NP

## The Argument

### Core Approach

Annila frames computational complexity through thermodynamic principles:

1. **Non-deterministic computation (NP)**:
   - State space evolves during computation
   - Computational decisions affect subsequent decision sets dynamically
   - Cannot be efficiently contracted by deterministic means
   - Requires "super-polynomial time" for deterministic solution

2. **Deterministic computation (P)**:
   - Achieves solution through "deterministic sequence of dissipative transformations"
   - State space can be efficiently contracted
   - Solution is "stationary" and verifiable in polynomial time

3. **Physical Interpretation**:
   - Computational time is "proportional to dissipation"
   - Complexity is related to entropy and state space contraction
   - P is inherently a subset of NP based on energy transformation principles

### Key Claims

1. State spaces in NP evolve during computation itself
2. Deterministic finite automata cannot efficiently contract these evolving state spaces
3. The "stationary" nature of P solutions enables polynomial-time verification
4. Therefore, P ⊂ NP (strict subset)

## The Error

### Critical Flaw: Lack of Formal Mathematical Proof

The fundamental error in Annila's attempt is that **it provides a physical/philosophical interpretation rather than a rigorous mathematical proof**. The attempt suffers from several critical issues:

### 1. **Informal Physical Analogies**

The paper uses thermodynamic concepts (entropy, dissipation, state space evolution) as **metaphors** for computational complexity, but does not:
- Provide formal definitions in computational complexity theory terms
- Establish rigorous mathematical mappings between physical and computational concepts
- Prove that the physical intuitions translate to formal computational statements

### 2. **Undefined or Imprecise Terms**

Key terms are not formally defined in computational complexity theory:
- "State space evolution during computation" - unclear what this means formally
- "Efficient contraction" - not defined in complexity-theoretic terms
- "Dissipative transformations" - no formal computational definition
- "Stationary state" - vague in computational context

### 3. **Missing Computational Model**

The argument does not:
- Work within a standard computational model (Turing machines, circuits, etc.)
- Formally define the relationship between NP non-determinism and "state space evolution"
- Prove that NP state spaces cannot be "contracted" deterministically in polynomial time
- Show why physical entropy considerations impose computational lower bounds

### 4. **Circular Reasoning**

The argument essentially assumes what it tries to prove:
- Claims NP state spaces "cannot be efficiently contracted" by P algorithms
- This is essentially **restating P ≠ NP**, not proving it
- No formal proof is given that efficient contraction is impossible

### 5. **Confusion of Verification and Decision**

The claim about "stationary states" being verifiable in polynomial time confuses:
- **Verification** (checking a solution with a certificate) - defines NP
- **Decision** (finding a solution) - defines P
- The paper does not rigorously show why verification implies anything about decision complexity

### 6. **No Barrier Analysis**

The approach does not address or overcome known barriers to proving P ≠ NP:
- **Relativization**: Would the thermodynamic argument relativize?
- **Natural Proofs**: Does the argument use properties that would be "natural proofs"?
- **Algebrization**: How does the physical perspective avoid algebrization barriers?

## Formalization Approach

Our formalization attempts to:

1. **Extract** any formalizable claims from the physical metaphors
2. **Identify** where the informal reasoning breaks down
3. **Demonstrate** that the core claims either:
   - Are trivial/tautological (restating definitions)
   - Are unprovable without additional assumptions
   - Rely on informal physical intuitions that don't translate to formal proofs

## Formalization Status

### Coq (`coq/AnnilaAttempt.v`)
- Models basic computational complexity classes (P, NP)
- Attempts to formalize "state space evolution" claims
- **Identifies the gap**: No way to prove state spaces "cannot be contracted" without assuming P ≠ NP

### Lean (`lean/AnnilaAttempt.lean`)
- Formalizes the structure of the argument
- Shows where informal physical reasoning would need formal proof
- **Identifies the gap**: Physical intuitions are not formal computational proofs

### Isabelle (`isabelle/AnnilaAttempt.thy`)
- Provides a structured representation of the attempted proof
- Clearly marks where additional (unprovable) assumptions would be needed
- **Identifies the gap**: The "thermodynamic contraction" claim is unproven

## Conclusion

Annila's attempt is **not a valid proof** of P ≠ NP because:

1. ❌ Uses informal physical metaphors instead of formal computational definitions
2. ❌ Does not work within a standard computational model
3. ❌ Assumes (rather than proves) that NP state spaces cannot be efficiently contracted
4. ❌ Provides no rigorous mathematical proof of the core claims
5. ❌ Does not address known barriers to proving P ≠ NP

### What This Shows

This formalization demonstrates an important lesson: **physical intuitions and metaphors**, while potentially useful for understanding, **are not substitutes for rigorous mathematical proofs** in computational complexity theory. A valid proof of P ≠ NP must:
- Work within formal computational models
- Provide rigorous mathematical arguments
- Address or circumvent known proof barriers

## References

1. Annila, A. (2009). "Physical portrayal of computational complexity", arXiv:0906.1084
2. Annila, A. (2012). "Physical portrayal of computational complexity", ISRN Computational Mathematics, ID: 321372, pp. 1-15
3. Woeginger, G. J. "The P-versus-NP page", https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
4. Cook, S. A. (1971). "The complexity of theorem-proving procedures", STOC 1971
5. Aaronson, S., Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory", STOC 2008

## Related Work

- [proofs/p_not_equal_np/](../../p_not_equal_np/README.md) - Framework for verifying P ≠ NP proof attempts
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](../../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of valid approaches
- [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md) - Tools for formal verification
