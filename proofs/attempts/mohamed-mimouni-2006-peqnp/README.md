# Mohamed Mimouni (2006) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #32](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 32 (from Woeginger's list)
- **Author**: Mohamed Mimouni
- **Year**: 2006 (August)
- **Claim**: P = NP
- **Language**: French
- **Status**: Refuted (comments by Radoslaw Hofman)
- **Source**: http://www.wbabin.net/science/mimouni.pdf (inaccessible as of 2026)

---

## Summary

Mohamed Mimouni's 2006 attempt claimed to prove P = NP by constructing a polynomial-time algorithm for the Clique Problem, which is NP-complete. The proof attempted to:

1. Define a polynomial-time algorithm for finding cliques in graphs
2. Conclude P = NP since Clique is NP-complete

The proof was **refuted through comments by Radoslaw Hofman** (now inaccessible at http://www.wbabin.net/comments/hofman.htm), which identified errors in the claimed algorithm.

---

## Directory Structure

This attempt follows the standard structure:

```
mohamed-mimouni-2006-peqnp/
├── README.md              # This file - overview of the attempt
├── original/              # Description of the original proof idea
│   └── README.md         # Detailed description of Mimouni's approach
├── proof/                 # The forward proof attempt formalization
│   ├── lean/             # Lean 4 formalization of the proof structure
│   │   └── MimouniProof.lean
│   └── rocq/             # Rocq formalization of the proof structure
│       └── MimouniProof.v
└── refutation/           # The refutation of the proof
    ├── README.md         # Explanation of why the proof fails
    ├── lean/             # Lean 4 formalization of the refutation
    │   └── MimouniRefutation.lean
    └── rocq/             # Rocq formalization of the refutation
        └── MimouniRefutation.v
```

---

## The Core Error

Mimouni's proof fails because the **claimed polynomial-time algorithm for Clique is invalid**.

### Why Clique-Based P=NP Attempts Fail

Without access to the original paper, we cannot identify the specific error. However, clique-based P=NP attempts consistently fail due to:

1. **Special Case Error**: Algorithm only works on specific graph families (dense graphs, small graphs) but not all graphs

2. **Exponential Time Disguised**: Algorithm runs in O(n^k) where k is clique size - this is NOT polynomial in input size

3. **Incorrect Complexity Analysis**: Errors in counting operations or analyzing loops

4. **Incomplete Algorithm**: Correctness bugs that miss valid cliques or report false positives

### Why Clique Remains Hard

- **NP-Completeness**: Proven by Karp in 1972
- **Hardness of Approximation**: Hastad (1999) showed Clique is hard to approximate within n^(1-epsilon)
- **50+ years of research**: No polynomial-time algorithm has been found despite extensive effort

---

## Formalization Details

### Original Proof Structure (`proof/`)

The `proof/` directory formalizes Mimouni's claimed argument:

1. **Clique Problem Definition**: Formal definition of the NP-complete Clique Problem
2. **`mimouni_clique_algorithm`**: Placeholder axiom for the claimed algorithm (unavailable)
3. **`mimouni_main_claim`**: The logical consequence showing P = NP if the algorithm existed

The formal structure shows that IF the axiom were true, P = NP would follow. However, the algorithm axiom is FALSE.

### Refutation (`refutation/`)

The `refutation/` directory demonstrates why the proof fails:

1. **`special_case_error`**: Why algorithms that only work on special cases don't prove P = NP
2. **`k_dependent_complexity_error`**: Why O(n^k) is not polynomial
3. **`incorrect_complexity_error`**: How complexity analysis errors invalidate proofs
4. **`incomplete_algorithm_error`**: Why incomplete algorithms don't suffice
5. **`clique_not_in_P_under_ETH`**: Under ETH, Clique is not in P

---

## Source Material Status

| Resource | URL | Status |
|----------|-----|--------|
| Original Paper | http://www.wbabin.net/science/mimouni.pdf | Inaccessible |
| Hofman's Comments | http://www.wbabin.net/comments/hofman.htm | Inaccessible |
| Woeginger's Entry | https://wscor.win.tue.nl/woeginger/P-versus-NP.htm | Available |

The original sources are no longer accessible. The domain (wbabin.net) is defunct and no archived versions could be found via Internet Archive or other archival services.

---

## Related Attempts

Other clique-based P=NP attempts share similar failure patterns:

- **Dhami et al. (2014)** - Attempt #97: Authors withdrew after acknowledging the algorithm failed on large instances
- **Various attempts (2000-2016)**: Multiple attempts using different approaches, all containing errors

---

## Lessons Learned

1. **Extraordinary Claims Require Extraordinary Proof**: P = NP would be one of the most important results in mathematics

2. **Common Error Patterns**: Clique-based attempts share predictable failure modes that can be checked for

3. **Peer Review is Essential**: The complexity theory community identified errors through Hofman's comments

4. **Source Availability Matters**: When sources become inaccessible, the scientific record is incomplete

---

## References

1. Woeginger, G. J. "The P-versus-NP page". Entry #32. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
2. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." Complexity of Computer Computations, pp. 85-103.
3. Garey, M.R., Johnson, D.S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness." W.H. Freeman.
4. Hastad, J. (1999). "Clique is hard to approximate within n^(1-epsilon)." Acta Mathematica.

---

## Status

- ✅ Original proof idea documented
- ✅ Lean 4 formalization (proof structure)
- ✅ Rocq formalization (proof structure)
- ✅ Lean 4 refutation
- ✅ Rocq refutation
- ✅ Error analysis complete
- ⚠️ Specific algorithm details unavailable (source inaccessible)

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #437](https://github.com/konard/p-vs-np/issues/437) | [PR #499](https://github.com/konard/p-vs-np/pull/499)
