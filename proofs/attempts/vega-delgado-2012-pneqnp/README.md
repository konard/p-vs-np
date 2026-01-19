# Vega Delgado (2012) - P≠NP Proof Attempt

**Attempt ID**: 83 (from Woeginger's list)
**Author**: Frank Vega Delgado
**Year**: 2012
**Claim**: P ≠ NP
**Status**: Refuted/Invalid

## Summary

In February 2012, Frank Vega Delgado claimed to prove that P is not equal to NP. His approach involves starting from the assumption that P = UP (where UP is the Unambiguous Polynomial time complexity class), and showing that this assumption leads to the consequence that EXP = P. Since EXP ≠ P is a well-established result from the Time Hierarchy Theorem, this creates a contradiction, which Vega Delgado argues implies that P ≠ UP. Since UP is a subclass of NP, this would suggest P ≠ NP.

## Main Argument

The proof structure follows this pattern:

1. **Assumption**: Suppose P = UP
2. **Derivation**: From P = UP, derive that EXP = P (the exact mechanism of this derivation is the critical step)
3. **Contradiction**: EXP = P contradicts the Time Hierarchy Theorem, which proves EXP ≠ P
4. **Conclusion**: By reductio ad absurdum, the assumption P = UP must be false, therefore P ≠ UP
5. **Final claim**: Since UP ⊆ NP, and P ≠ UP, this implies P ≠ NP

## Complexity Classes Involved

- **P**: Problems solvable in deterministic polynomial time
- **UP**: Unambiguous Polynomial time - NP problems where accepting computations are unique (if they exist)
- **NP**: Nondeterministic Polynomial time
- **EXP (EXPTIME)**: Problems solvable in deterministic exponential time (2^poly(n))

## Known Issues and Refutation

### Logical Gap in the Argument

The main error in this proof attempt lies in the derivation step (step 2 above). The proof fails to rigorously establish why P = UP would necessarily imply EXP = P. This is a substantial logical gap:

1. **Unjustified implication**: The connection between P = UP and EXP = P is not properly demonstrated through valid reductions or complexity-theoretic arguments
2. **Missing intermediate steps**: The proof does not provide the necessary chain of reductions or constructions to bridge P = UP to EXP = P
3. **Invalid reasoning about complexity class collapses**: Even if P = UP, this does not automatically imply arbitrary complexity class collapses

### Additional Problems

1. **UP ⊂ NP does not imply P ≠ UP leads to P ≠ NP**: Even if P ≠ UP were proven, this alone would not prove P ≠ NP. It would only show that P is strictly contained in UP, but we would still need to prove UP = NP or that there exists a problem in NP \ UP that requires superpolynomial time. The relationship between UP and NP is itself non-trivial.

2. **Circular reasoning risk**: The proof may implicitly assume properties about complexity class separations that are equivalent to what it's trying to prove

3. **Lack of formal rigor**: The arguments are presented informally without rigorous mathematical proofs of the key claims

### Publication History

- The paper "The existence of one-way functions" was available at http://the-point-of-view-of-frank.blogspot.com/
- A variant appeared under the title "P versus UP" in the IEEE Latin America Transactions
- A version was submitted to arXiv under the pseudonym "Asia Furones" and was withdrawn by arXiv administrators due to violation of arXiv's policy against pseudonyms
- The proof has not been accepted by the complexity theory community

### Related Work

Frank Vega Delgado has submitted multiple papers over the years claiming solutions to P vs NP, with different and sometimes contradictory conclusions (both P = NP and P ≠ NP in different papers). This pattern raises concerns about the rigor and validity of the approaches.

## Formalization Goal

The goal of this formalization is to:

1. Formalize the structure of the claimed proof in Rocq, Lean, and Isabelle
2. Identify precisely where the proof breaks down or requires unjustified assumptions
3. Make explicit the gaps in reasoning that prevent the proof from being valid
4. Document the error in a rigorous, machine-checkable way

## Expected Outcome

When formalizing this proof attempt, we expect to encounter one or more of the following:

1. **Unprovable lemma**: A step claiming P = UP → EXP = P that cannot be proven without additional (likely false) assumptions
2. **Type error or logical inconsistency**: Attempting to use complexity classes or reductions in ways that don't type-check or make logical sense
3. **Circular dependency**: Assumptions that implicitly require what we're trying to prove
4. **Missing reduction**: A claim about polynomial-time reductions that cannot be constructively demonstrated

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #83)
- Time Hierarchy Theorem: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms"
- UP complexity class: Valiant, L. G. (1976). "Relative complexity of checking and evaluating"

## Formalization Structure

```
vega-delgado-2012-pneqnp/
├── README.md (this file)
├── rocq/
│   └── VegaDelgado2012.v         - Rocq formalization
├── lean/
│   └── VegaDelgado2012.lean      - Lean 4 formalization
└── isabelle/
    └── VegaDelgado2012.thy       - Isabelle/HOL formalization
```

Each formalization will:
- Define the relevant complexity classes (P, UP, NP, EXP)
- State the Time Hierarchy Theorem as an axiom
- Attempt to formalize the claimed proof steps
- Document where the proof fails with explicit `sorry`/`admit`/`oops` markers
