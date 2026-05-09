# Amar Mukherjee (2011) - P=NP via Polynomial-Time 3-SAT Algorithm

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 73 (from Woeginger's list)
- **Author**: Amar Mukherjee
- **Year**: 2011 (submitted April 2011, withdrawn January 2012)
- **Claim**: P = NP
- **Paper**: "The 3-satisfiability problem"
- **Source**: arXiv:1104.4490
- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #73)

## Summary

In April 2011, Amar Mukherjee submitted a paper to arXiv claiming to present a **deterministic polynomial-time algorithm for 3-SAT** (the 3-satisfiability problem). Since 3-SAT is NP-complete, a correct polynomial-time algorithm would establish P = NP.

The paper was **withdrawn by the author in January 2012**, with a note that "a revision has been developed," indicating that the author found issues requiring reworking. No corrected version was ever published.

## The Main Argument

Mukherjee claimed to provide a deterministic polynomial-time algorithm that solves 3-SAT. The 3-SAT problem consists of:

- **Input**: A Boolean formula in conjunctive normal form (CNF) where each clause has exactly 3 literals
- **Output**: A satisfying assignment of Boolean variables, or a declaration that no such assignment exists
- **Status**: NP-complete (Cook 1971, Levin 1973)

The key claim was that a deterministic (non-probabilistic, non-heuristic) algorithm could decide any 3-SAT instance in time bounded by a polynomial in the input size.

## Why 3-SAT is Hard

### NP-Completeness of 3-SAT

3-SAT is the canonical NP-complete problem. Any problem in NP can be reduced to 3-SAT in polynomial time (Cook-Levin theorem). This means:
- A polynomial-time algorithm for 3-SAT would solve ALL problems in NP in polynomial time
- This would prove P = NP, resolving the most famous open problem in computer science

### Why Deterministic Polynomial Algorithms Fail for 3-SAT

The difficulty of 3-SAT stems from:

1. **Exponential Search Space**: With n Boolean variables, there are 2ⁿ possible assignments to check
2. **No Known Efficient Shortcut**: There is no known way to prune the search space to polynomial size while guaranteeing correctness
3. **Belief P ≠ NP**: Most complexity theorists believe no polynomial-time algorithm exists for 3-SAT (and hence for NP-complete problems generally)
4. **Decades of Failed Attempts**: Thousands of researchers have tried to find polynomial-time algorithms for NP-complete problems without success

### The Core Difficulty

For a CNF formula with n variables and m clauses:
- **Satisfying assignments**: Can be 0 to 2ⁿ (any subset of the 2ⁿ variable assignments)
- **Verifying one assignment**: O(m) time (polynomial)
- **Finding one**: Requires searching through potentially exponential candidates
- **Shortcuts**: Any shortcut that doesn't enumerate all candidates must somehow exploit structural properties that are not known to exist in general

## The Error

Without access to the full paper (it was withdrawn from arXiv), the precise error cannot be pinpointed. However, based on the pattern of similar P=NP claims for NP-complete problems (especially SAT), the most common categories of error are:

### Category 1: Incorrect Reduction or Transformation

Many P=NP attempts transform an NP-complete problem into another formulation and claim the new formulation is easier. The error typically is:
- The transformation is correct but the new problem is still NP-hard
- The transformation is incorrect (loses essential information, adds extra assumptions)

### Category 2: Algorithm Incorrectness

The claimed algorithm may:
- Only work on special cases (sparse instances, bounded treewidth, etc.) but not general 3-SAT
- Contain a logical error that causes it to sometimes return incorrect answers
- Have a complexity analysis error (the runtime is not actually polynomial)

### Category 3: Hidden Exponential

A common subtle error is hiding exponential computation:
- The algorithm description looks polynomial but implicitly performs exponential search
- A data structure has exponential size that is not accounted for
- A subroutine is called an exponential number of times

### Author's Own Acknowledgment

The withdrawal of the paper with note "a revision has been developed" strongly suggests the author discovered a flaw themselves. The fact that no corrected version was ever published indicates the flaw was fundamental rather than technical.

## Broader Context

### 3-SAT and NP-Completeness

3-SAT was the first problem proven NP-complete (Cook 1971). It is:
- **Decision version**: Is there an assignment that satisfies all clauses?
- **Search version**: Find such an assignment if it exists
- **Optimization version**: Find an assignment satisfying the maximum number of clauses (MAX-SAT)

All three versions are NP-complete (or NP-hard for optimization).

### Known Algorithms for 3-SAT

The best known algorithms for 3-SAT:
- **Brute force**: O(2ⁿ · mn) - exponential
- **DPLL algorithm**: O(1.84ⁿ) in worst case - still exponential
- **Modern SAT solvers**: Practical tools that work well on instances arising in practice, but remain exponential in the worst case

No polynomial-time deterministic algorithm is known.

### The P vs NP Question

The question of whether P = NP remains open. The scientific consensus is:
- **Most complexity theorists believe P ≠ NP**
- No proof in either direction exists
- A correct proof of P = NP would need to withstand scrutiny from the entire theoretical computer science community

## Formalization Goals

In this directory, we formalize:

1. **The 3-SAT Problem**: Formal definition and why it is NP-complete
2. **The Exponential Search Space**: Why checking all 2ⁿ assignments cannot be avoided in general
3. **The Cook-Levin Theorem**: Why 3-SAT is NP-complete
4. **Why Polynomial-Time 3-SAT Would Imply P=NP**: The central consequence
5. **The Structural Barrier**: Why no polynomial shortcut is known to exist

The formalizations capture what CAN be formalized about the approach and document where the claimed proof encounters fundamental barriers.

## References

### Primary Sources

- **Original Claim**: Mukherjee, A. (2011). "The 3-satisfiability problem"
  - arXiv:1104.4490
  - Submitted: April 2011; Withdrawn: January 5, 2012

### NP-Completeness Background

- **Cook, S.A.** (1971). "The complexity of theorem proving procedures." *STOC 1971*, pp. 151-158.
- **Levin, L.A.** (1973). "Universal search problems." *Problems of Information Transmission*, 9(3), 265-266.
- **Karp, R.M.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, pp. 85-103.

### Context

- **Woeginger's List**: Entry #73
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Related Issue**: #44 (general P vs NP framework)

## Key Lessons

1. **Withdrawal Is Significant**: When authors withdraw P=NP claims, it typically means a fundamental error was found
2. **3-SAT Is the Benchmark**: Any claim to solve 3-SAT in polynomial time must be carefully scrutinized
3. **Complexity Barriers Are Real**: Decades of effort have not found polynomial-time algorithms for NP-complete problems
4. **The Cook-Levin Legacy**: The NP-completeness of 3-SAT means any such claim implies P=NP

## See Also

- [P = NP Framework](../../) - General framework for evaluating P vs NP claims
- [Repository README](../../../README.md) - Overview of the P vs NP problem
