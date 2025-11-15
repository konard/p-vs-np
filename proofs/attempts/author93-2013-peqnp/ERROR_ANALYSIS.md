# Error Analysis: Maknickas (2013) P=NP Attempt

## Executive Summary

**Error Type**: Fundamental confusion between LP and ILP
**Severity**: Critical - invalidates the entire approach
**Status**: ❌ Claim is incorrect

## The Claim

Maknickas (2013) claims to prove P=NP by:
1. Encoding the NP-complete SAT problem as a linear programming problem
2. Using polynomial-time LP solvers to solve SAT
3. Concluding that SAT ∈ P, therefore P=NP

## The Critical Error

### The Conflation

The paper **conflates** two fundamentally different problems:

1. **Linear Programming (LP)**
   - Variables can be **real numbers** (continuous)
   - Solvable in **polynomial time** ✓
   - Complexity class: **P-complete**
   - Examples: Simplex, Interior Point methods

2. **Integer Linear Programming (ILP)**
   - Variables must be **integers** (discrete)
   - **NP-complete** problem ✗
   - Requires exponential time (unless P=NP)
   - Cannot be solved efficiently in general

### Why This Matters for SAT

**SAT requires discrete solutions**: Boolean satisfiability needs assignments where each variable is either TRUE (1) or FALSE (0).

Any encoding of SAT as an optimization problem must enforce that solutions are **boolean (0 or 1)**, which means:
- Solutions must be **integer-valued**
- This makes the problem **Integer Linear Programming**
- ILP is **NP-complete** itself!

### The Dilemma

Any attempt to encode SAT as LP faces an unavoidable choice:

**Option 1: Use integer constraints**
- Variables must be in {0, 1}
- Result: Integer Linear Programming (ILP)
- Complexity: NP-complete
- **Outcome**: No polynomial-time algorithm (unless P=NP already)

**Option 2: Allow fractional values**
- Variables can be any real number
- Result: True Linear Programming (LP)
- Complexity: Polynomial-time ✓
- **Problem**: Solutions may be fractional (e.g., x=0.5)
- **Outcome**: Fractional solutions are **not valid boolean assignments**

## Concrete Counterexample

Consider the formula: `(x ∨ y) ∧ (¬x ∨ ¬y)`

**Valid boolean solutions**:
- x=0, y=1 ✓
- x=1, y=0 ✓

**Naive LP encoding**:
- Constraint 1: `x + y ≥ 1` (from x ∨ y)
- Constraint 2: `x + y ≤ 1` (from ¬x ∨ ¬y)

**LP relaxation solution**:
- x=0.5, y=0.5 ✓ (satisfies LP constraints)
- **But**: x=0.5 is **not a boolean value**
- **Cannot** be directly converted to a SAT solution

This demonstrates that LP relaxation allows invalid solutions.

## What the Paper Fails to Prove

The paper **does not prove** that:
1. The LP formulation always produces integer (boolean) solutions
2. Fractional LP solutions can be efficiently rounded to integer solutions
3. The encoding size remains polynomial when enforcing integer constraints

Without proving one of these, the approach fails.

## Why This is a Common Mistake

This error appears repeatedly in attempted P vs NP proofs because:

1. **LP is familiar**: Many people know LP can be solved efficiently
2. **ILP looks similar**: Syntactically, ILP is just "LP + integer constraints"
3. **The gap is subtle**: It's easy to overlook that integer constraints change complexity
4. **Wish fulfillment**: The approach "feels like" it should work

## Well-Known Theoretical Results

### What We Know

1. **LP ∈ P**: Khachiyan (1979), Karmarkar (1984)
   - Ellipsoid method and interior point methods are polynomial-time

2. **ILP is NP-complete**: Karp (1972)
   - Deciding feasibility of ILP is NP-complete
   - Optimization version is NP-hard

3. **SAT is NP-complete**: Cook (1971)
   - The first problem proven NP-complete

4. **SAT → ILP reduction**: Standard result
   - SAT can be encoded as ILP with polynomial size
   - But this doesn't help because ILP is also NP-complete

5. **LP relaxations**: Used in approximation algorithms
   - Can give approximate solutions for some problems
   - Cannot solve NP-complete problems exactly in polynomial time

### Impossibility Results

**Hofman (2006)**: "Why Linear Programming cannot solve large instances of NP-complete problems in polynomial time"
- Proves that polynomial-time LP solutions to NP-complete problems cannot exist (unless P=NP)
- Common errors: exponential formulations, hidden integer constraints, problem modification

**Fiorini et al. (2015)**: Exponential lower bounds for extended formulations
- Some polytopes require exponentially many linear constraints
- Limits on what can be expressed efficiently with LP

## Formalization Summary

Our formal proofs in **Coq**, **Lean**, and **Isabelle** demonstrate:

1. ✓ **SAT requires boolean assignments** (discrete)
2. ✓ **LP may produce fractional solutions** (counterexample shown)
3. ✓ **Integer constraints → ILP** (NP-complete)
4. ✓ **The dilemma is unavoidable** (proven formally)

### Key Theorems Proven

**Theorem 1 (Fractional Solutions Exist)**:
```
∃ formula, LP_encoding, assignment:
  LP_solution(encoding, assignment) ∧
  ¬ boolean_assignment(assignment)
```
Proven with concrete example: x=0.5, y=0.5

**Theorem 2 (Integer Constraints → ILP)**:
```
∀ encoding:
  requires_integer_constraints(encoding) →
  encoding_is_ILP(encoding)
```

**Theorem 3 (The Dilemma)**:
```
∀ SAT_encoding:
  requires_integer_constraints(encoding) ∨
  may_have_fractional_solutions(encoding)
```

## Conclusion

**The error is fundamental and fatal to the proof.**

Maknickas's approach cannot prove P=NP because:
1. With integer constraints → Solves ILP (NP-complete, not polynomial-time)
2. Without integer constraints → May produce invalid fractional solutions

**Educational Value**: This formalization serves as:
- A clear example of the LP/ILP distinction
- A warning about this common proof attempt pattern
- A demonstration of formal verification catching subtle errors

## References

1. Maknickas, A.A. (2013). "Linear Programming Formulation of Boolean Satisfiability Problem"
2. Cook, S.A. (1971). "The complexity of theorem-proving procedures"
3. Karp, R.M. (1972). "Reducibility among combinatorial problems"
4. Khachiyan, L.G. (1979). "A polynomial algorithm in linear programming"
5. Hofman, R. (2006). "Why Linear Programming cannot solve large instances of NP-complete problems"
6. Fiorini, S., et al. (2015). "Exponential Lower Bounds for Polytopes in Combinatorial Optimization"
