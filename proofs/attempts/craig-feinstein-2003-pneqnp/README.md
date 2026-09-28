# Craig Alan Feinstein (2003-04) - P≠NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #11](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 11 (from Woeginger's list)
- **Author**: Craig Alan Feinstein
- **Year**: 2003-04
- **Claim**: P ≠ NP
- **Status**: Withdrawn by author (counterexample found)
- **Source**: arXiv (2003-04 submissions, withdrawn)

---

## Summary

Craig Alan Feinstein's 2003-04 attempt claimed to prove P ≠ NP by working within a "restricted model of computation." The proof attempted to:

1. Define a restricted computational model
2. Prove exponential lower bounds for NP-complete problems within this model
3. Transfer these lower bounds to general Turing machine computation

The proof was **withdrawn by the author after a counterexample was discovered**, demonstrating that the transfer principle (step 3) is invalid.

---

## Directory Structure

This attempt follows the standard structure:

```
craig-feinstein-2003-pneqnp/
├── README.md              # This file - overview of the attempt
├── original/              # Description of the original proof idea
│   ├── README.md         # Detailed description of Feinstein's approach
│   └── paper/            # References to original papers
│       └── REFERENCES.md
├── proof/                 # The forward proof attempt formalization
│   ├── lean/             # Lean 4 formalization of the proof structure
│   │   └── FeinsteinProof.lean
│   └── rocq/             # Rocq formalization of the proof structure
│       └── FeinsteinProof.v
└── refutation/           # The refutation of the proof
    ├── README.md         # Explanation of why the proof fails
    ├── lean/             # Lean 4 formalization of the refutation
    │   └── FeinsteinRefutation.lean
    └── rocq/             # Rocq formalization of the refutation
        └── FeinsteinRefutation.v
```

---

## The Core Error

Feinstein's proof fails because the **transfer principle is FALSE**:

> Lower bounds in restricted computational models do NOT automatically imply lower bounds in general Turing machine computation.

This is a fundamental issue with all restricted model approaches to P vs NP.

### Why the Transfer Fails

1. **Restricted models forbid techniques**: By definition, a restricted model limits what operations algorithms can use

2. **General computation has more tools**: Turing machines can use techniques unavailable in the restricted model

3. **The dilemma**:
   - If the restricted model exactly captures polynomial-time computation, proving lower bounds is as hard as P vs NP itself
   - If the model is genuinely restricted, the transfer principle fails

### Analogy: Sorting

- In the comparison-based model: Sorting requires Ω(n log n) comparisons
- In general computation: Radix sort achieves O(n) time
- The comparison lower bound doesn't transfer to general computation!

---

## Formalization Details

### Original Proof Structure (`proof/`)

The `proof/` directory formalizes Feinstein's claimed argument:

1. **`feinsteinRestrictedLowerBound`**: Exponential lower bound in the restricted model
2. **`feinsteinTransferPrinciple`**: The (false) claim that restricted bounds transfer
3. **`feinsteinConclusion`**: The logical consequence combining (1) and (2)

The formal structure shows that IF the axioms were true, P ≠ NP would follow. However, the transfer principle axiom is FALSE.

### Refutation (`refutation/`)

The `refutation/` directory demonstrates why the proof fails:

1. **`transferPrincipleFails`**: The transfer principle is provably false
2. **`claimGap`**: The gap between what restricted models show vs. what's claimed
3. **`counterexampleInvalidatesTransfer`**: How counterexample algorithms break the proof

---

## Historical Context

Feinstein's 2003-04 work was part of a broader pattern of attempts using restricted models. Similar approaches include:

- Decision tree lower bounds
- Circuit complexity with restrictions
- Communication complexity arguments

All of these have the same fundamental limitation: restricted model lower bounds don't transfer to unrestricted computation.

### Feinstein's Other Work

Around the same period, Feinstein published other papers making strong claims:
- "The Riemann Hypothesis is Unprovable" (2003)
- "The Collatz 3n+1 Conjecture is Unprovable" (2003)

These share a pattern of making strong claims that, under scrutiny, contain logical gaps.

---

## Lessons Learned

1. **Intellectual Honesty**: Feinstein withdrew the paper when the error was found, demonstrating scientific integrity

2. **Restricted Models Have Limits**: Lower bounds in restricted models are conditional and don't generalize

3. **Transfer Principles Are Hard**: The gap between restricted and general models is a fundamental barrier in complexity theory

---

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #11. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Feinstein, C. A. (2003-04). P vs NP attempts (withdrawn)
3. Feinstein, C. A. (2003). "The Riemann Hypothesis is Unprovable". arXiv:math/0309367
4. Feinstein, C. A. (2003). "The Collatz 3n+1 Conjecture is Unprovable". arXiv:math/0312309

---

## Status

- ✅ Original proof idea documented
- ✅ Lean 4 formalization (proof structure)
- ✅ Rocq formalization (proof structure)
- ✅ Lean 4 refutation
- ✅ Rocq refutation
- ✅ Error analysis complete

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #434](https://github.com/konard/p-vs-np/issues/434) | [PR #496](https://github.com/konard/p-vs-np/pull/496)
