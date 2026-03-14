# Original Paper: Javaid Aslam (2008)

## Paper Information

**Title**: "An Extension of the Permutation Group Enumeration Technique (Collapse of the Polynomial Hierarchy: NP = P)"

**Author**: Javaid Aslam

**Submission Date**: December 7, 2008

**Latest Version**: October 30, 2017 (version 26)

**arXiv ID**: arXiv:0812.1385

**Primary Classification**: Computational Complexity (cs.CC), Data Structures and Algorithms (cs.DS)

## Abstract

The paper claims to present a polynomial-time enumerable partition of potential perfect matchings in bipartite graphs using a structure called "MinSet Sequence". The author argues this enables enumeration of perfect matchings in polynomial time with complexity O(n^45 log n), and consequently claims to prove "NP = P" and "#P = FP."

## Main Approach (from the paper)

### The Core Idea

1. **Problem**: Count perfect matchings in a bipartite graph G with n vertices on each side
2. **Challenge**: Complete bipartite graphs have n! perfect matchings (exponential)
3. **Proposed Solution**: Use a "MinSet Sequence" structure to enumerate all matchings in polynomial time
4. **Claimed Complexity**: O(n^45 log n) time

### The MinSet Sequence

The paper proposes a data structure that:
- Partitions potential matchings into equivalence classes
- Uses concepts from symmetric group theory
- Claims to polynomial-size representation of exponential information
- Allegedly enumerates all perfect matchings by iterating through this structure

### The Claimed Implications

If correct, this would mean:
1. **#P = FP**: All counting problems in #P solvable in polynomial time
2. **P = NP**: Immediately follows from #P = FP
3. **Polynomial Hierarchy Collapse**: Entire hierarchy collapses to P

## Why This Paper is Controversial

### Multiple Revisions

- 26+ versions over 9 years (2008-2017)
- Highly unusual for a mathematical paper
- Suggests ongoing issues with the proof

### Refutation Published

In 2009, a refutation paper (arXiv:0904.3912) was published showing:
- A specific counter-example graph where the algorithm fails
- The algorithm does not correctly count all perfect matchings
- Fundamental issues with the MinSet Sequence approach

### Community Reception

- Not accepted by the complexity theory community
- Multiple counter-examples published
- No independent verification of correctness

## Files

- **ORIGINAL.pdf**: The original paper by Javaid Aslam (arXiv:0812.1385v26)
- **REFUTATION.pdf**: The refutation paper "Refutation of Aslam's Proof that NP = P" (arXiv:0904.3912)

## References

- **Original paper**: https://arxiv.org/abs/0812.1385
- **Refutation**: https://arxiv.org/abs/0904.3912
- **Author's response**: https://arxiv.org/abs/0906.5112
- **Woeginger's P vs NP list, entry #50**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Note

This document provides a high-level summary of the original paper. For full technical details, refer to ORIGINAL.pdf. The formalization in the `proof/` directory captures the logical structure of the argument, while the `refutation/` directory addresses why it fails.
