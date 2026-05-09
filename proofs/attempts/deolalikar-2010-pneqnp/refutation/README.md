# Refutation: Deolalikar's P≠NP Attempt (2010)

This directory contains formalizations of the known errors in Deolalikar's 2010 P≠NP manuscript.

## Overview of Failures

Deolalikar's proof failed at multiple independent points. Below we describe each error and how it is formalized.

## Error 1: FO+LFP Locality Does Not Imply Polylog-Parameterizability

**The claimed step**: Deolalikar argued that because FO+LFP formulas satisfy Gaifman locality (local formulas depend only on bounded-radius neighborhoods), the solution spaces they define must be "polylog-parameterizable."

**Why it fails**:
- Gaifman's theorem applies to *first-order* formulas, giving a local normal form
- FO+LFP adds the *least fixed point* operator, which can propagate information globally through iteration
- The fixed point iteration can encode global information that is NOT captured by local neighborhoods alone
- Terence Tao and others noted that Deolalikar's argument tacitly assumed that LFP does not break locality, which is false in general

**Example**: Consider a formula that checks graph connectivity via a fixed point computation: "x is reachable from source s." This is expressible in FO+LFP but is a global property not captured by any bounded neighborhood.

## Error 2: The Ordered Structure Requirement

**The claimed step**: Deolalikar applied the Immerman-Vardi theorem (FO+LFP captures P over ordered structures) to encode k-SAT.

**Why it fails**:
- The Immerman-Vardi theorem requires the structures to be *ordered* (equipped with a linear order)
- Deolalikar's encoding of k-SAT formulas as structures was not clearly presented as ordered structures in the relevant technical sense
- The choice of ordering can affect what FO+LFP can express, so the argument is sensitive to encoding details that were not specified

## Error 3: Random Instances vs. Worst-Case Complexity

**The claimed step**: Properties of typical random k-SAT instances (near the satisfiability threshold) imply that k-SAT ∉ P.

**Why it fails**:
- Computational complexity is about *worst-case* instances, not average-case or typical instances
- A polynomial-time algorithm for k-SAT does not need to "navigate" the solution space clustering — it only needs to output YES or NO
- The fact that the solution space of a random instance is complex does not prevent a P algorithm from deciding satisfiability
- A P algorithm might recognize structural properties of satisfiable instances without enumerating solutions
- Russell Impagliazzo and others emphasized this fundamental gap between average-case properties and worst-case complexity

## Error 4: The Parameterizability Lower Bound Was Not Proved

**The claimed step**: Hard k-SAT solution spaces are not polylog-parameterizable.

**Why it fails**:
- Deolalikar needed to show a *lower bound*: that no polylog-parameter encoding exists for hard k-SAT solution spaces
- Lower bounds in complexity theory are notoriously difficult
- The manuscript did not provide a rigorous argument for this lower bound
- Terence Tao specifically noted this gap: the clustering structure (many separated components) does not automatically imply high parameterization complexity — one might still be able to parameterize the union of clusters efficiently

## Error 5: Circular Reasoning

Some reviewers noted that parts of the argument appeared to assume complexity-theoretic separations in order to prove P ≠ NP, which is circular.

## Files

- `lean/DeolalikarRefutation.lean` — Lean 4 formalization of the errors
- `rocq/DeolalikarRefutation.v` — Rocq/Coq formalization of the errors

## References

- Tao's blog: https://terrytao.wordpress.com/2010/08/10/on-deolalikar%E2%80%99s-attempted-proof-that-p%E2%89%A0np/
- Aaronson's blog: https://www.scottaaronson.com/blog/?p=456
- Lipton's blog: https://rjlipton.wordpress.com/2010/08/08/a-proof-that-p-is-not-equal-to-np/
