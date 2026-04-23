# Frank Vega Delgado (2010) - P≠NP Proof Attempt

**Attempt ID**: 68 (from Woeginger's list)
**Author**: Frank Vega Delgado
**Year**: 2010 (November)
**Claim**: P ≠ NP
**Status**: Refuted/Invalid

## Summary

In November 2010, Frank Vega Delgado claimed to prove that P is not equal to NP. His approach involves investigating the relationship between complexity classes through properties of one-way functions and unambiguous computation, claiming to show that the assumption P = NP leads to a contradiction via the existence of certain cryptographic constructs.

The central argument uses properties of one-way functions (functions easy to compute but hard to invert) and their relationship to complexity classes. The claim is that if P = NP, then one-way functions cannot exist, but the proof argues (without sufficient rigor) that they must exist, yielding a contradiction.

## Core Argument

The proof structure follows this pattern:

1. **Assumption**: Suppose P = NP
2. **One-Way Functions**: Argue that if P = NP, then no one-way functions exist (since inverting any function would become a polynomial-time computable operation)
3. **Existence Claim**: Claim that one-way functions must exist (via a constructive argument or complexity-theoretic argument)
4. **Contradiction**: The non-existence and existence claims contradict each other
5. **Conclusion**: Therefore P ≠ NP

## Complexity and Cryptographic Concepts Involved

- **P**: Problems solvable in deterministic polynomial time
- **NP**: Decision problems verifiable in polynomial time
- **One-way functions**: Functions `f` where computing `f(x)` is easy (polynomial time) but inverting `f` (given `f(x)`, finding any `x'` with `f(x') = f(x)`) is hard (superpolynomial time)
- **P = NP implication for crypto**: If P = NP, then inverting functions becomes polynomial, destroying all one-way functions

## Known Issues and Refutation

### Critical Error: Unjustified Existence of One-Way Functions

The existence of one-way functions is itself an **open problem** in complexity theory:
- It is known that if P = NP, then one-way functions do not exist
- It is **not** known that one-way functions actually exist — their existence would imply P ≠ NP (the converse is conditional)
- The proof circularly assumes what it tries to prove: showing one-way functions "must exist" is essentially the same as showing P ≠ NP

### Circularity

The argument structure is circular:
- To show one-way functions exist, the proof implicitly assumes P ≠ NP (or uses assumptions equivalent to it)
- Then uses this to derive P ≠ NP

### Lack of Formal Rigor

The arguments in the 2010 paper are presented informally without rigorous mathematical proofs of the key claims. The connection between the existence of one-way functions and complexity class separation is not formally established.

### Comparison with the 2012 Attempt

Frank Vega Delgado made a different, though similarly flawed, argument in 2012 (Woeginger entry #83, see [`../vega-delgado-2012-pneqnp/`](../vega-delgado-2012-pneqnp/)). The 2012 paper uses UP = P → EXP = P style argument, while the 2010 paper focuses on one-way functions. Both fail for different reasons.

## Formalization Structure

```
frank-vega-delgado-2010-pneqnp/
├── README.md (this file)
├── original/
│   └── ORIGINAL.md               - Description of the original paper
├── proof/
│   ├── README.md                 - Explanation of proof formalization
│   ├── lean/
│   │   └── VegaDelgado2010Proof.lean
│   └── rocq/
│       └── VegaDelgado2010Proof.v
└── refutation/
    ├── README.md                 - Explanation of refutation
    ├── lean/
    │   └── VegaDelgado2010Refutation.lean
    └── rocq/
        └── VegaDelgado2010Refutation.v
```

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #68)
- One-way functions and P vs NP: Impagliazzo, R. (1995). "A personal view of average-case complexity." Proceedings of the 10th Annual Structure in Complexity Theory Conference.
- Related issue: #44
