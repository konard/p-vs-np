# Jason W. Steinmetz (2011) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Attempts](../)

**Attempt ID:** 75
**Author:** Jason W. Steinmetz
**Year:** 2011
**Claim:** P=NP
**Paper Title:** "Algorithm that Solves 3-SAT in Polynomial Time"
**arXiv Link:** http://arxiv.org/abs/1110.1658 (withdrawn)
**Status:** Withdrawn by author

---

## Summary

In October 2011, Jason W. Steinmetz claimed to establish P=NP by presenting a polynomial time algorithm for solving the NP-complete 3-SAT problem. The paper was submitted to arXiv as 1110.1658. However, the paper was subsequently **withdrawn by the author** with the final revision in June 2015.

## Main Argument/Approach

The paper claimed to provide an algorithm that solves the 3-satisfiability (3-SAT) problem in polynomial time. Since 3-SAT is an NP-complete problem (proven by Cook in 1971 and Karp in 1972), a polynomial-time algorithm for 3-SAT would imply P=NP by the definition of NP-completeness: all problems in NP can be reduced to 3-SAT in polynomial time, so a polynomial-time solution for 3-SAT would give polynomial-time solutions for all NP problems.

The specific details of the algorithm are not publicly available since the paper has been withdrawn and the PDF is no longer accessible on arXiv.

## Known Refutation

The paper was **withdrawn by the author himself**. According to the arXiv abstract page, the withdrawal reason states:

> "the integer operations within the algorithm cannot be proven to have a polynomial run time."

This is a critical flaw that invalidates the polynomial-time claim.

## The Error in the Proof

The fundamental error identified by the author is that **the integer arithmetic operations used in the algorithm cannot be guaranteed to run in polynomial time**. This is a common pitfall in complexity theory proofs.

### Why This is Critical

In computational complexity theory, when analyzing algorithm runtime:

1. **Model of Computation Matters**: The standard model is the Turing machine (or equivalent RAM model with uniform cost measure or logarithmic cost measure)

2. **Integer Operations Are Not Always O(1)**:
   - On a **uniform cost RAM**: all operations on integers of arbitrary size count as O(1) - but this model is unrealistic for very large integers
   - On a **logarithmic cost RAM** (more realistic): operations on n-bit integers take O(n) time minimum
   - On a **Turing machine**: operating on n-bit integers requires at least O(n) steps

3. **The Problem**: If the algorithm requires operations on integers whose bit-length grows super-polynomially with the input size, then even basic operations (addition, comparison, etc.) on these integers will require super-polynomial time

4. **Common Trap**: Many attempted proofs of P=NP or P≠NP fail to account for the true cost of arithmetic operations when integer sizes grow during the algorithm's execution

### Formalization Goal

The formalizations in this directory aim to:

1. Model the claim that 3-SAT can be solved in polynomial time
2. Formalize what it means for integer operations to have polynomial runtime bounds
3. Show that the existence of a polynomial-time 3-SAT algorithm implies P=NP
4. Identify the gap: an algorithm that uses integer operations without proven polynomial bounds does not establish P=NP

## Structure

This directory contains formal verification attempts in multiple proof assistants:

- `coq/` - Coq formalization
- `lean/` - Lean 4 formalization
- `isabelle/` - Isabelle/HOL formalization

Each subdirectory contains:
- Definitions of 3-SAT, polynomial time, and the claim structure
- Formalization of the gap: unbounded integer operations
- Documentation of the error

## Key Insights

This attempt illustrates several important lessons for P vs NP research:

1. **Computational Model Precision**: Any algorithm claiming polynomial runtime must specify its computational model and account for all operation costs

2. **Integer Size Growth**: Algorithms that manipulate integers must bound their growth to ensure operations remain polynomial-time

3. **Verification is Essential**: The author's self-withdrawal demonstrates the importance of rigorous verification - even the proposer couldn't ultimately justify the polynomial-time claim

4. **Common Pitfall**: This is not an isolated case - many P=NP attempts fail due to hidden super-polynomial costs in "elementary" operations

## References

### Primary Source
- **Steinmetz, J.W.** (2011). "Algorithm that Solves 3-SAT in Polynomial Time." arXiv:1110.1658 [cs.CC] (withdrawn)
- Withdrawal note: "the integer operations within the algorithm cannot be proven to have a polynomial run time"

### Background
- **Woeginger's P-versus-NP page**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #75)
- **Cook, S.** (1971). "The complexity of theorem-proving procedures." *STOC*
- **Karp, R.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*

### Computational Models
- **Aho, A.V., Hopcroft, J.E., Ullman, J.D.** (1974). *The Design and Analysis of Computer Algorithms*
- **Arora, S., Barak, B.** (2009). *Computational Complexity: A Modern Approach* (Chapter 1: The Computational Model)

## Status

- ✅ README documentation: Complete
- ✅ Coq formalization: Complete
- ✅ Lean 4 formalization: Complete
- ✅ Isabelle/HOL formalization: Complete

---

**Related:** [P = NP Framework](../../p_eq_np/) | [Issue #48](https://github.com/konard/p-vs-np/issues/48) | [Parent Issue #44](https://github.com/konard/p-vs-np/issues/44)
