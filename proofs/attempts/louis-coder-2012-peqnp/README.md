# Louis Coder (Matthias Michael Mueller) 2012 - P=NP Claim

**Attempt ID**: 91 (from Woeginger's list)
**Author**: Louis Coder (Matthias Michael Mueller)
**Year**: 2012 (updated 2020)
**Claim**: P=NP
**Paper**: "Polynomial Exact-3-SAT-Solving Algorithm"
**Source**: http://vixra.org/abs/1212.0109

## Summary

In December 2012, Louis Coder (Matthias Michael Mueller) published a paper claiming to solve 3-SAT in polynomial time O(n^15), which would imply P=NP. The algorithm, called "Algorithm E-1.0" in its final version, uses a polynomial-space array to track which 3-SAT clauses could potentially appear in a satisfying assignment, using nested loops to check consistency constraints.

## Main Argument/Approach

The algorithm works as follows:

1. **Data Structure**: Maintains a boolean array `Active[PC

Num]` where `PCNum = O(n³)` is the number of possible 3-SAT clauses over n variables
2. **Initialization**: All `Active[]` values start as `true`
3. **Iterative Refinement**: Uses 4 nested loops (i, j, k, l) iterating over all possible clauses, setting `Active[i] := false` when there don't exist CNF-absent, active, non-conflicting clauses j, k, l in appropriate blocks
4. **Result**: If any `Active[]` value remains `true` in the last block, the CNF is declared satisfiable; otherwise UNSAT

The key claim is that by checking "local consistency" through these nested loops and reaching a state of "the same 0/1 chars in each clause path column," the algorithm can determine satisfiability without exploring the exponential space of all 2^n truth assignments.

## The Error in the Proof

The fundamental error in this P=NP claim is that **local consistency does not imply global satisfiability for 3-SAT**. Specifically:

### Error 1: Insufficient Information Encoding

The `Active[]` array can only store O(n³) bits of information (one bit per possible 3-SAT clause). However, the satisfiability problem for 3-SAT requires tracking information about 2^n possible truth assignments. By the pigeonhole principle, this polynomial-sized encoding cannot distinguish between all possible satisfiability scenarios.

**Formalization**: The encoding loses exponential information. If the algorithm were correct, it would provide a polynomial-time reduction from an NP-complete problem to a problem solvable with O(n³) bits of state, violating the space hierarchy theorem under standard complexity assumptions.

### Error 2: Local vs. Global Consistency

The algorithm checks that clauses are "not in conflict" pairwise and across blocks, achieving a property called "the same 0/1 chars in each clause path column." However, this is merely a local consistency property.

**Counterexample Sketch**: Consider a 3-SAT formula where:
- Locally, every small subset of clauses is satisfiable
- Globally, the entire formula is UNSAT due to long-range dependencies

The algorithm's polynomial loops cannot capture these long-range global constraints because they only check bounded-size combinations of clauses.

### Error 3: The "Exponential Solver Simulation" Fallacy

The paper claims the polynomial solver "simulates" an exponential solver by storing the same information in 3-SAT clauses rather than m-SAT clauses (where m can grow up to n). However:

- The exponential solver needs to track potentially 2^n different "active solutions" (partial assignments)
- The polynomial solver only tracks O(n³) boolean values
- The claim that "the same 0/1 chars in each clause path column" property allows this compression is unfounded

**The Flaw**: The paper assumes without proof that whenever the exponential solver would maintain certain active solutions, the polynomial solver's `Active[]` array will correctly encode this. But there's no bijection between:
- The exponential set of partial assignments the exponential solver maintains
- The polynomial set of active clauses the polynomial solver tracks

### Error 4: Complexity Analysis Oversight

The paper claims O(n^15) complexity but this only counts loop iterations, not the actual computational complexity of determining satisfiability. The real issue is:

- **What the loops do**: Check whether certain combinations of clauses exist
- **What they can't do**: Verify that these local combinations extend to a global satisfying assignment
- **Missing step**: The algorithm never actually constructs or verifies a truth assignment; it only checks clause-level compatibility

### Error 5: The "While Loop" Doesn't Fix Global Issues

The algorithm uses a `while (ChangesExisting)` loop to propagate constraint information until a fixed point. The paper claims this captures all necessary

 inference. However:

- This is essentially a form of unit propagation / forward checking
- It's well-known that unit propagation alone is incomplete for 3-SAT
- No amount of polynomial-time iteration can overcome the exponential search space without additional insights

## Known Refutation

This work has not been accepted by the complexity theory community because:

1. **No peer review**: Published only on viXra (preprint server), never in peer-reviewed venue
2. **Fundamental impossibility**: If correct, would solve a Clay Millennium Prize Problem
3. **Lack of rigorous proof**: The "proof of correctness" section contains logical gaps and unsubstantiated claims
4. **Barrier violations**: Doesn't address how it circumvents known barriers (relativization, natural proofs, algebrization)
5. **Empirical testing limitations**: Testing on instances with n ≤ 26 is insufficient (exponential algorithms can handle such small instances easily)

Mihai Prunescu analyzed an earlier version and noted issues with the approach.

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Coq**: Formalizing the claim that local consistency implies global satisfiability and showing this leads to a contradiction
2. **Lean**: Constructing an explicit counterexample formula where the algorithm's `Active[]` array would incorrectly indicate satisfiability
3. **Isabelle**: Proving that the information-theoretic bound prevents polynomial-space encoding of exponential satisfiability information

## References

- Original paper: http://vixra.org/pdf/1212.0109vD.pdf (Version E-1.0, 2020)
- Author's website: https://www.louis-coder.com/
- Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #91)
- Prunescu analysis: "About a Surprising Computer Program of Matthias Müller" (2014)

## Implementation Note

The author provides C++ implementations that reportedly work on test cases. However, this doesn't validate correctness because:
- Small test cases (n ≤ 26) can be solved by exponential algorithms in reasonable time
- The implementation may contain bugs that accidentally make it work on test cases
- Empirical testing cannot prove polynomial-time correctness for all inputs

The fact that it correctly solved some instances doesn't prove P=NP, just as a backtracking SAT solver working on small instances doesn't prove it runs in polynomial time.
