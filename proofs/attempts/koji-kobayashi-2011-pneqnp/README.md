# Koji Kobayashi (2011) - P != NP via CHAOS Dependency Relations

**Attempt ID**: 78 (from Woeginger's live list)
**Author**: Koji Kobayashi
**Year**: 2011
**Claim**: P != NP
**Status**: Refuted/Invalid

## Summary

Kobayashi's 2011 paper, "NP is not AL and P is not NC is not NL is not L",
claims the strict chain

```text
NP > AL = P > NC > NL > L
```

The argument introduces "combined problems" whose element problems depend on
other element problems. The main constructed languages are `CHAOS`, `ORDER`,
`LAYER`, and `TWINE`. Kobayashi claims that these dependency structures witness
strict separations between standard complexity classes.

## Main Argument

The proof attempts to proceed by constructing increasingly restricted
dependency patterns:

1. `CHAOS`: a combined problem where every element problem depends on the whole
   combined problem. Kobayashi claims `CHAOS in NP` but `CHAOS notin AL`.
2. `ORDER`: a linear dependency pattern. Kobayashi claims `ORDER in P` but
   `ORDER notin NC`.
3. `LAYER`: a layered partial order dependency pattern. Kobayashi claims
   `LAYER in NC` but `LAYER notin NL`.
4. `TWINE`: a bounded dependency pattern with rotating paths. Kobayashi claims
   `TWINE in NL` but `TWINE notin L`.

If all of these claims were valid, they would separate `NP` from `P` and also
separate several lower complexity classes.

## Known Issues and Refutation

The proof fails because the paper does not give formal language definitions,
machine encodings, input-size accounting, or reductions strong enough to justify
the class membership and non-membership claims.

The critical gap is the conversion from an informal dependency graph into a
complexity-class lower bound. In standard complexity theory, showing that one
particular representation or evaluation discipline uses too much space does not
prove that no log-space, alternating-log-space, NC, or polynomial-time algorithm
exists for the same language.

The proof also uses several invalid or unsupported moves:

- It treats cyclic dependency descriptions as evidence that an alternating
  log-space computation cannot exist.
- It assumes that a machine must materialize all dependency values or all
  dependency paths.
- It identifies `AL` with `P`, but then uses informal machine-composition
  arguments instead of the standard theorem's actual simulation.
- It argues lower bounds against selected procedures rather than against all
  algorithms in the target class.

## Formalization Structure

```text
koji-kobayashi-2011-pneqnp/
├── README.md
├── original/
│   ├── README.md
│   ├── ORIGINAL.md
│   └── ORIGINAL.pdf
├── proof/
│   ├── README.md
│   ├── lean/
│   │   └── Kobayashi2011Proof.lean
│   └── rocq/
│       └── Kobayashi2011Proof.v
└── refutation/
    ├── README.md
    ├── lean/
    │   └── Kobayashi2011Refutation.lean
    └── rocq/
        └── Kobayashi2011Refutation.v
```

## References

- Woeginger's P-versus-NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #78)
- Koji Kobayashi, "NP is not AL and P is not NC is not NL is not L", arXiv:1110.0200
- Chandra, Kozen, and Stockmeyer, "Alternation", Journal of the ACM, 1981
