# Author 11 (2004) - P=NP Attempt

**Authors**: Selmer Bringsjord and Joshua Taylor
**Year**: 2004 (arXiv submission: June 28, 2004)
**Claim**: P=NP
**Source**: arXiv:cs/0406056
**Entry**: #11 on Woeginger's P vs NP attempts list

## Summary

Bringsjord and Taylor claim to resolve the P=?NP problem via a "formal argument" for P=NP. However, they acknowledge that their approach is a "meta-level argument" rather than the expected "object-level proof" typically required to resolve the P vs NP problem.

The core of their argument relies on demonstrating that a known NP-complete problem can be solved via a simple physical process, which they argue shows that P=NP.

## Main Argument/Approach

The paper presents a meta-level philosophical argument that:

1. Takes a known NP-complete problem (likely SAT or a similar problem)
2. Proposes a physical process/mechanism that can allegedly solve this problem in polynomial time
3. Concludes that since an NP-complete problem can be solved in polynomial time via this physical mechanism, P=NP

The authors explicitly acknowledge in their paper:
- "The expected format of a solution is an object-level proof, not a meta-level argument like what we provide"
- The paper includes revisions marked in red responding to commentators' criticisms

## Known Refutation

### Main Error: Smuggling in Exponentially Growing Hardware

The fatal flaw in this argument, pointed out by the second commentator (as acknowledged by the authors' red-annotated revisions), is that **the physical process requires exponentially growing hardware**.

Specifically:
1. The physical mechanism they propose to solve the NP-complete problem requires hardware resources that grow exponentially with input size
2. This violates the fundamental constraint of the P vs NP question, which concerns **polynomial time on a standard computational model** (Turing machine or equivalent)
3. The argument conflates:
   - Physical parallelism with unbounded resources → Can solve NP problems "quickly" with enough hardware
   - Computational complexity on a standard model → Requires polynomial time with polynomial space

### The Core Confusion

The paper makes a **categorical error** between:
- **Physical computation**: With exponentially many physical components, one can solve NP-complete problems in polynomial wall-clock time
- **Computational complexity**: Concerns algorithmic efficiency on a standard computational model with polynomial resources

This is similar to claiming "I can solve SAT in O(1) time by building a circuit with 2^n gates that tries all assignments in parallel" - technically true but irrelevant to the P vs NP question.

## The Error in Formalization

When we attempt to formalize this argument, the error becomes immediately apparent:

1. **Assumption**: There exists a physical process P that solves an NP-complete problem L in polynomial time
2. **Hidden assumption**: This physical process uses exponentially many physical resources (e.g., components, parallel processors)
3. **Invalid conclusion**: Since physical process P solves L quickly, L ∈ P

The formalization reveals that:
- The polynomial time bound only applies when resources are also polynomially bounded
- The physical process violates the resource constraints implicit in the definition of P
- The argument proves nothing about the classical P vs NP question

## Formalization Status

This directory contains formalizations in:
- **Coq**: Demonstrates the invalid reasoning by showing the hidden exponential resource assumption
- **Lean**: Formalizes the gap between physical processes and computational complexity classes
- **Isabelle**: Proves that the argument relies on an unproven (and likely false) assumption about polynomial resources

All three formalizations identify the same core error: **conflating physical parallelism with computational efficiency in the P vs NP framework**.

## References

- arXiv:cs/0406056 - "P=NP" by Selmer Bringsjord and Joshua Taylor (2004)
- Woeginger's P vs NP attempts list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Scott Aaronson's "Eight Signs A Claimed P≠NP Proof Is Wrong" discusses similar errors

## Notes

The authors themselves acknowledged their argument was non-standard ("meta-level" rather than "object-level"), and they revised the paper in response to criticisms about exponentially growing hardware. This suggests awareness that their argument had fundamental issues, though they appeared to believe these could be addressed while maintaining their conclusion.

The formalization work in this directory demonstrates why such physical arguments cannot resolve the P vs NP question without first establishing that the physical process uses only polynomial resources - a claim that would itself require proving P=NP to justify.
