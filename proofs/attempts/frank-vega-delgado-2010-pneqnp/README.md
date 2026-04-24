# Frank Vega Delgado (2010) - P≠NP Proof Attempt

**Attempt ID**: 68 (from Woeginger's list)
**Author**: Frank Vega Delgado
**Year**: 2010 (November)
**Claim**: P ≠ NP
**Status**: Refuted/Invalid

## Summary

The November 2010 attempt is the paper `A Solution to the P versus NP Problem` (arXiv:1011.2730). Its core idea is to define a search problem called `CERTIFYING`: given a deterministic Turing machine and an output, find an input that produces that output.

The paper claims that `CERTIFYING` is in NP and argues that if it were also in P, then NP would contain an undecidable problem. That would contradict basic computability facts, so the paper concludes P ≠ NP.

## Core Argument

The proof structure follows this pattern:

1. **Define CERTIFYING**: Given a deterministic Turing machine and an output, ask for an input that realizes the output.
2. **Show membership in NP**: A candidate input can be checked efficiently.
3. **Claim the critical step**: If `CERTIFYING` were in P, then some undecidable language would belong to NP.
4. **Derive contradiction**: NP languages are decidable, so an undecidable language cannot be in NP.
5. **Conclusion**: Therefore `CERTIFYING` is not in P and P ≠ NP.

## Complexity and Computability Concepts Involved

- **P**: Problems solvable in deterministic polynomial time
- **NP**: Decision problems verifiable in polynomial time
- **Decidable language**: A language with a total algorithm that always halts with the correct yes/no answer
- **Undecidable language**: A language for which no such total algorithm exists
- **CERTIFYING**: The paper'"'"'s search/decision hybrid problem, where one seeks an input producing a specified output from a deterministic machine

## Known Issues and Refutation

### Critical Error: Unsupported Leap to an Undecidable NP Language

The paper never rigorously shows that `CERTIFYING ∈ P` would force an undecidable language into NP:

- It does not exhibit a concrete undecidable language and a valid reduction
- It does not formalize why the ability to solve `CERTIFYING` efficiently would change decidability
- It conflates a search-style problem with a complexity-class separation argument

### Circular or Unjustified Reasoning

The argument only works if the missing implication is true, but that implication is exactly what the paper tries to establish.

### Lack of Formal Rigor

The 2010 paper is informal on the crucial computability-theoretic step. It does not provide a machine-checked proof or a fully precise reduction from `CERTIFYING` to an undecidable language.

### Comparison with the 2012 Attempt

Frank Vega Delgado made a different, though similarly flawed, argument in 2012 (Woeginger entry #83, see [`../vega-delgado-2012-pneqnp/`](../vega-delgado-2012-pneqnp/)). The 2012 paper uses a `P = UP → EXP = P` style argument, while the 2010 paper focuses on `CERTIFYING` and undecidability. Both fail for different reasons.

## Formalization Structure

```
frank-vega-delgado-2010-pneqnp/
├── README.md (this file)
├── original/
│   ├── README.md                - Description of the original paper
│   ├── ORIGINAL.md              - Markdown reconstruction of the paper
│   └── ORIGINAL.pdf             - Source arXiv PDF
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
- Vega Delgado, F. (2010). `A Solution to the P versus NP Problem` (arXiv:1011.2730)
- Related issue: #44
