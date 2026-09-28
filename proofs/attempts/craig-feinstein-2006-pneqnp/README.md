# Craig Alan Feinstein (2006) - P!=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #31](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 31 (from Woeginger's list)
- **Author**: Craig Alan Feinstein
- **Year**: 2006
- **Claim**: P != NP
- **Status**: Refuted by circular dependency in the counting argument
- **Source**: "A New and Elegant Argument that P is not NP"

---

## Summary

This directory records Craig Alan Feinstein's separate 2006 attempt titled
"A New and Elegant Argument that P is not NP". It is distinct from the older
2003-04 withdrawn Feinstein attempt in
`proofs/attempts/craig-feinstein-2003-pneqnp/`, which corresponds to
Woeginger entry #11.

The 2006 argument is presented as a short combinatorial proof. In abstract
form, it tries to:

1. Encode accepting computations or candidate certificates as a large search
   space.
2. Assert that any polynomial-time algorithm can inspect or distinguish only a
   small part of that space.
3. Conclude that an NP-complete language therefore needs super-polynomial time.

The gap is that step 2 assumes the algorithm must use the same undirected
search strategy that the proof counts. A polynomial-time verifier or solver may
exploit structure, reductions, dynamic programming, algebraic identities, or
other compressed representations. Counting many possible certificates does not
by itself prove a lower bound against all polynomial-time Turing machines.

---

## Directory Structure

```
craig-feinstein-2006-pneqnp/
├── README.md
├── original/
│   ├── README.md
│   └── ORIGINAL.md
├── proof/
│   ├── README.md
│   ├── lean/
│   │   └── Feinstein2006Proof.lean
│   └── rocq/
│       └── Feinstein2006Proof.v
└── refutation/
    ├── README.md
    ├── lean/
    │   └── Feinstein2006Refutation.lean
    └── rocq/
        └── Feinstein2006Refutation.v
```

---

## Formalization Details

The forward formalization records the claimed proof pattern as conditional
axioms:

- a large family of candidate witnesses exists;
- every polynomial-time algorithm is assumed to distinguish too few candidates;
- the lower bound is then transferred to an NP-complete language.

The refutation formalization isolates the missing premise. A search-space
counting lower bound applies only after proving that every polynomial-time
algorithm must behave like the counted search process. That premise is not
established, so the conclusion does not follow.

---

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #31. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Feinstein, C. A. (2006). "A New and Elegant Argument that P is not NP".

---

## Status

- Original proof idea reconstructed in Markdown
- Lean 4 proof-structure formalization
- Rocq proof-structure formalization
- Lean 4 refutation skeleton
- Rocq refutation skeleton

