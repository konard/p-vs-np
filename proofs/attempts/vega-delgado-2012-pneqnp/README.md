# Vega Delgado (2012) - P≠NP Proof Attempt

**Attempt ID**: 83 (from Woeginger's list)
**Author**: Frank Vega Delgado
**Year**: 2012 (February)
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
- **UP**: Unambiguous Polynomial time — NP problems where accepting computations are unique (if they exist)
- **NP**: Nondeterministic Polynomial time
- **EXP (EXPTIME)**: Problems solvable in deterministic exponential time (2^poly(n))

## Known Issues and Refutation

### Critical Error: Unjustified Implication (P = UP → EXP = P)

The main error lies in the derivation step (step 2 above). The proof fails to rigorously establish why P = UP would necessarily imply EXP = P:

1. **Unjustified implication**: No known complexity-theoretic result connects P = UP to EXP = P
2. **Missing intermediate steps**: No chain of reductions or constructions is provided to bridge P = UP to EXP = P
3. **Unconditional separation**: The Time Hierarchy Theorem already separates EXP from P unconditionally; P = UP cannot change this

### Secondary Error: Insufficient Conclusion (P ≠ UP ↛ P ≠ NP)

Even if P ≠ UP could be proven, this alone would not prove P ≠ NP:
- We know P ⊆ UP ⊆ NP, but not whether UP = NP
- The relationship between UP and NP is itself an open problem
- Additional work is needed to bridge the gap from P ≠ UP to P ≠ NP

### Publication History

- The paper "The existence of one-way functions" was available at http://the-point-of-view-of-frank.blogspot.com/
- A variant appeared under the title "P versus UP" in the IEEE Latin America Transactions
- A version was submitted to arXiv under the pseudonym "Asia Furones" and was withdrawn by arXiv administrators for violating arXiv's policy against pseudonyms
- The proof has not been accepted by the complexity theory community

### Related Work

Frank Vega Delgado submitted multiple papers over the years with different and sometimes contradictory conclusions (both P = NP and P ≠ NP in different papers). See also the November 2010 attempt (Woeginger #68) and the June 2015 attempt.

## Formalization Structure

```
vega-delgado-2012-pneqnp/
├── README.md (this file)
├── original/
│   └── ORIGINAL.md               - Description of original paper
├── proof/
│   ├── README.md                 - Explanation of proof formalization
│   ├── lean/
│   │   └── VegaDelgado2012Proof.lean
│   └── rocq/
│       └── VegaDelgado2012Proof.v
└── refutation/
    ├── README.md                 - Explanation of refutation
    ├── lean/
    │   └── VegaDelgado2012Refutation.lean
    └── rocq/
        └── VegaDelgado2012Refutation.v
```

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #83)
- Time Hierarchy Theorem: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms"
- UP complexity class: Valiant, L. G. (1976). "Relative complexity of checking and evaluating"
