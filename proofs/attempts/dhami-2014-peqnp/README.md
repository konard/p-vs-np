# Dhami et al. (2014) - P=NP Attempt

**Attempt ID**: 97 (from Woeginger's list)
**Authors**: Pawan Tamta, B.P. Pande, H.S. Dhami
**Year**: 2014
**Claim**: P = NP
**Status**: **Refuted** (2015)

## Overview

In February 2014, Pawan Tamta, B.P. Pande, and H.S. Dhami published a paper claiming to prove P=NP by constructing a polynomial-time algorithm for the NP-complete Clique Problem.

## Main Argument

The authors' approach consisted of the following steps:

1. **Reduction to Maximum Flow Network Interdiction Problem (MFNIP)**: They claimed that the Clique Problem can be reduced to the Maximum Flow Network Interdiction Problem.

2. **Polynomial-Time Algorithm**: They proposed a polynomial-time algorithm for solving the resulting MFNIP instance.

3. **Conclusion**: Since the Clique Problem is NP-complete, a polynomial-time algorithm for it would imply P = NP.

## The Error

The proof attempt contains fundamental flaws that were identified through:

1. **Self-Withdrawal**: The original paper (arXiv:1403.1178) was withdrawn by the authors themselves. The arXiv entry notes "an error while applying the algorithm to large size problems," indicating the algorithm fails to work correctly on larger instances.

2. **Published Refutation**: In April 2015, Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, and Nathaniel S. Potrepka published a formal refutation titled "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami" (arXiv:1504.06890).

### Key Issues

The main problems with the proof include:

1. **Algorithm Correctness**: The proposed algorithm does not correctly solve the Clique Problem for all instances, particularly failing on larger problem sizes.

2. **Reduction Validity**: The claimed reduction to MFNIP and/or the algorithm for solving MFNIP contains errors that make the overall approach unsound.

3. **Complexity Analysis**: Even if the algorithm were correct, the complexity analysis may not properly account for all steps, potentially resulting in super-polynomial time complexity.

## Formal Verification Strategy

This directory contains formalizations in three proof assistants (Coq, Lean, and Isabelle) that:

1. **Define the Clique Problem** formally as a decision problem.
2. **Define the Maximum Flow Network Interdiction Problem** formally.
3. **Formalize the claimed reduction** from Clique to MFNIP.
4. **Identify the error** by demonstrating either:
   - A counterexample where the reduction fails
   - A proof that the algorithm is not polynomial-time
   - A proof that the algorithm does not correctly solve all instances

## Educational Value

This attempt demonstrates important lessons:

1. **Reductions Must Be Sound**: A reduction must correctly transform all instances, not just some examples.
2. **Correctness vs. Heuristics**: An algorithm that works on small or typical cases is not necessarily correct for all cases.
3. **Complexity Analysis**: Careful analysis is needed to ensure all steps truly run in polynomial time.
4. **Peer Review**: The self-correction (withdrawal) and external refutation show the scientific process working correctly.

## References

1. **Original Paper**: Pawan Tamta, B.P. Pande, H.S. Dhami. "A Polynomial Time Solution to the Clique Problem." arXiv:1403.1178 (2014, withdrawn).
   - https://arxiv.org/abs/1403.1178

2. **Related Work**: Pawan Tamta, B.P. Pande, H.S. Dhami. "Reduction of Maximum Flow Network Interdiction Problem from The Clique Problem." arXiv:1402.2022 (2014).
   - https://arxiv.org/abs/1402.2022

3. **Refutation**: Hector A. Cardenas, Chester Holtz, Maria Janczak, Philip Meyers, Nathaniel S. Potrepka. "A Refutation of the Clique-Based P=NP Proofs of LaPlante and Tamta-Pande-Dhami." arXiv:1504.06890 (2015).
   - https://arxiv.org/abs/1504.06890

4. **Woeginger's List**: Entry #97
   - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Structure

```
dhami-2014-peqnp/
├── README.md           # This file
├── coq/               # Coq formalization
│   └── Dhami2014.v    # Main proof file
├── lean/              # Lean 4 formalization
│   └── Dhami2014.lean # Main proof file
└── isabelle/          # Isabelle/HOL formalization
    └── Dhami2014.thy  # Main theory file
```

## See Also

- Parent issue: [#44 - Test all P vs NP attempts formally](https://github.com/konard/p-vs-np/issues/44)
- This attempt: [#313 - Formalize: Dhami (2014) - P=NP](https://github.com/konard/p-vs-np/issues/313)
- General P=NP framework: [proofs/p_eq_np/](../../p_eq_np/)
