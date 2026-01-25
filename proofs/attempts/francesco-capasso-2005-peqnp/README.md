# Francesco Capasso (2005) - P=NP Attempt

**Attempt ID**: 23
**Author**: Francesco Capasso
**Year**: 2005
**Claim**: P=NP
**Paper**: http://arxiv.org/abs/cs.CC/0511071
**Status**: Refuted (author revised claim from "algorithm" to "heuristic")

## Summary

In November 2005, Francesco Capasso claimed to have constructed a polynomial-time algorithm for Circuit-SAT, which would imply P=NP. The paper went through several revisions on arXiv:

- **Versions 1-3** (Nov 18, 22, 23, 2005): "A polynomial-time algorithm for Circuit-SAT"
- **Version 4+** (Nov 28, 2005 onwards): "A polynomial-time heuristic for Circuit-SAT"

The title change from "algorithm" to "heuristic" indicates that the author recognized the approach does not actually solve all instances correctly in polynomial time, which would be required for a valid P=NP proof.

## Main Argument

The paper proposes a polynomial-time procedure for determining the satisfiability of circuits with three possible outcomes:

1. Prove the circuit is a tautology (always true)
2. Prove the circuit is a contradiction (always false)
3. Find a satisfying input assignment

The algorithm is claimed to run in polynomial time and space relative to the input dimension.

## The Error

**Critical Flaw**: A heuristic is not an algorithm that solves all instances correctly.

The fundamental error in this proof attempt is the confusion between:

1. **Polynomial-time algorithm**: A procedure that correctly solves ALL instances of a problem in polynomial time
2. **Polynomial-time heuristic**: A procedure that may work well on many instances but does NOT guarantee correct solutions for all inputs

For a valid proof that P=NP, one must provide an algorithm that:
- Runs in polynomial time on ALL inputs (not just "most" or "typical" inputs)
- Produces the CORRECT answer for ALL inputs (not just "probably correct" or "correct with high probability")

The fact that the author revised the title from "algorithm" to "heuristic" demonstrates that the proposed method does not meet these requirements. A heuristic may:
- Fail to terminate in polynomial time on some inputs
- Produce incorrect results on some inputs
- Require exponential time in worst-case scenarios

This is a common error in P vs NP proof attempts: proposing an approach that works well in practice or on many instances, but failing to prove it works correctly and efficiently on ALL possible instances.

## Known Refutation

The self-refutation is implicit in the author's title change from "algorithm" to "heuristic" in Version 4. This indicates acknowledgment that the method does not constitute a complete polynomial-time algorithm for Circuit-SAT.

**Source**: Woeginger's P versus NP page (https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), Entry #23

## Formalization Goal

This formalization demonstrates the distinction between:
1. A polynomial-time algorithm (which would prove P=NP if it existed for Circuit-SAT)
2. A polynomial-time heuristic (which does not prove P=NP)

The formalization shows that the existence of a heuristic is not sufficient to establish P=NP, and that the claim requires a complete algorithm with provable polynomial-time bounds on ALL inputs.

## Files

- `rocq/CapassoAttempt.v` - Rocq formalization showing the gap in the proof
- `lean/CapassoAttempt.lean` - Lean formalization showing the gap in the proof
- `isabelle/CapassoAttempt.thy` - Isabelle formalization showing the gap in the proof

## References

1. Francesco Capasso (2005). "A polynomial-time heuristic for Circuit-SAT". arXiv:cs.CC/0511071
2. Woeginger, G. J. "The P versus NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Thanks to Luca Trevisan for documenting this attempt

## Related

- Parent issue: #44 (Test all P vs NP attempts formally)
- This formalization: Issue #115
