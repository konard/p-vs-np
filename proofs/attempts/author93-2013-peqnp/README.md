# Formalization: Maknickas (2013) - P=NP via Linear Programming

**Attempt ID**: 93 from Woeginger's list
**Author**: Algirdas Antano Maknickas
**Year**: 2013
**Claim**: P=NP (SAT can be solved in polynomial time)
**Status**: ❌ Incorrect (Fundamental error identified)

## Overview

In March 2013, at the International Conference on Advances in Engineering Technologies and Physical Science in Hong Kong, Algirdas Antano Maknickas presented a paper titled "Linear Programming Formulation of Boolean Satisfiability Problem" published by Springer Science.

**Main Claim**: The author claims to translate the NP-hard satisfiability problem (SAT) into a polynomially-solvable linear programming problem, which would imply P=NP.

## Paper Details

- **Title**: Linear Programming Formulation of Boolean Satisfiability Problem
- **Conference**: International Conference on Advances in Engineering Technologies and Physical Science
- **Location**: Hong Kong
- **Publisher**: Springer Science (Lecture Notes in Electrical Engineering, Vol. 275)
- **Publication Date**: December 1, 2013
- **DOI**: 10.1007/978-94-007-7684-5_22
- **Affiliation**: Vilnius Gediminas Technical University, Vilnius, Lithuania

## The Approach

Maknickas's approach consists of the following steps:

1. **Multi-valued Logic Formulation**: Uses analytical expressions of multi-valued logic to represent Boolean formulas
2. **2SAT Formulation**: First formulates 2SAT as a linear programming optimization problem
3. **Extension to kSAT**: Extends the same linear programming formulation to 3SAT and general kSAT
4. **Claim**: Proposes that kSAT is in P and can be solved in linear time using this LP formulation

### Key Technical Claims

The paper claims that by using "new analytic multi-valued logic expressions," any kSAT instance can be:
- Encoded as a linear program with polynomial-size constraints
- Solved in polynomial time using standard LP algorithms (e.g., interior point methods)
- This solution can be converted back to a satisfying assignment

## The Critical Error

**The fundamental flaw**: The paper conflates **linear programming (LP)** with **integer linear programming (ILP)**.

### Why This Matters

1. **Linear Programming (LP)**:
   - Decision variables can take **real values** (continuous)
   - Solvable in **polynomial time** (P-complete)
   - Algorithms: Simplex, Ellipsoid method, Interior point methods

2. **Integer Linear Programming (ILP)**:
   - Decision variables must be **integers**
   - **NP-complete** problem
   - Cannot be solved in polynomial time unless P=NP

### The Gap in the Proof

**Critical issue**: Boolean satisfiability requires **boolean (0/1) assignments**, which are discrete/integer values.

Any correct formulation of SAT as a linear programming problem must:
1. Either use **integer constraints** (making it ILP, which is NP-complete)
2. Or provide a **proof** that the LP relaxation (allowing fractional solutions) always has an integer optimal solution

**What the paper fails to do**:
- The paper does not prove that the LP formulation always produces integer solutions
- If the LP allows fractional solutions, then the solution may not correspond to a valid boolean assignment
- Without integer constraints, the problem changes fundamentally
- With integer constraints, the problem becomes ILP, which is NP-complete

### Concrete Example of the Problem

Consider a simple SAT formula: `(x ∨ y) ∧ (¬x ∨ ¬y)`

**Correct satisfying assignments** (boolean):
- `x=0, y=1` (satisfies both clauses)
- `x=1, y=0` (satisfies both clauses)

**LP relaxation might produce**: `x=0.5, y=0.5`
- This satisfies LP constraints if formulated naively
- But `x=0.5, y=0.5` is **not a valid boolean assignment**
- Cannot be directly converted to a SAT solution

### Why This is a Common Error

This is a well-known pitfall in complexity theory:
- **Theorem**: Every NP problem can be formulated as an ILP with polynomial-size encoding
- **But**: ILP itself is NP-complete
- **The error**: Assuming that because LP is in P, an LP formulation of SAT would solve it in P
- **The reality**: A correct formulation requires integer constraints, making it ILP (NP-complete)

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the LP/ILP distinction clearly** in formal terms
2. **Showing that SAT requires discrete solutions** (boolean assignments)
3. **Proving that any LP formulation either**:
   - Uses integer constraints (making it ILP, thus NP-complete), OR
   - Produces potentially fractional solutions (not valid for SAT)
4. **Constructing a counterexample** where LP relaxation gives fractional solutions

## Related Work and Context

### Correct Results About LP and SAT

- **LP is in P**: Linear programming can be solved in polynomial time (Khachiyan 1979, Karmarkar 1984)
- **ILP is NP-complete**: Integer linear programming is NP-complete (Karp 1972)
- **LP relaxations**: Used in approximation algorithms for NP-hard problems, but don't solve them exactly
- **Extended formulations**: Fiorini et al. (2015) proved exponential lower bounds for certain polytope formulations

### Why LP Cannot Solve NP-Complete Problems

Hofman (2006) in "Why Linear Programming cannot solve large instances of NP-complete problems in polynomial time" explains:
- Any claim of polynomial-time LP solution to NP-complete problems must have a fundamental error
- Typically the error involves either:
  - Exponentially-sized formulations
  - Integer constraints (making it ILP)
  - Incorrect encoding that changes the problem

## References

1. Maknickas, A.A. (2013). "Linear Programming Formulation of Boolean Satisfiability Problem". In: Transactions on Engineering Technologies. Lecture Notes in Electrical Engineering, vol 275. Springer.
2. Cook, S.A. (1971). "The complexity of theorem-proving procedures". STOC 1971.
3. Karp, R.M. (1972). "Reducibility among combinatorial problems". Complexity of Computer Computations.
4. Khachiyan, L.G. (1979). "A polynomial algorithm in linear programming". Soviet Mathematics Doklady.
5. Hofman, R. (2006). "Why Linear Programming cannot solve large instances of NP-complete problems in polynomial time". arXiv:cs/0611008
6. Fiorini, S., et al. (2015). "Exponential Lower Bounds for Polytopes in Combinatorial Optimization". Journal of the ACM.
7. Woeginger, G.J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Formalization Files

- **Coq**: `coq/MaknickasAttempt.v` - Formalizes the LP/ILP distinction and the error
- **Lean**: `lean/MaknickasAttempt.lean` - Demonstrates the gap in the proof
- **Isabelle**: `isabelle/MaknickasAttempt.thy` - Provides counterexample with fractional solutions

## Conclusion

**The error**: Maknickas's approach conflates LP (polynomial-time solvable) with ILP (NP-complete).

**Why it fails**: Boolean satisfiability inherently requires discrete (integer) solutions. Any formulation that:
- Uses integer constraints is ILP (NP-complete, not polynomial-time)
- Doesn't use integer constraints may produce fractional solutions (invalid for SAT)

**Educational value**: This attempt illustrates a common misconception about the relationship between LP, ILP, and NP-completeness. Understanding this distinction is fundamental to computational complexity theory.

---

**Status**: Error formally identified and documented
**Conclusion**: The claim P=NP is incorrect due to LP/ILP conflation
