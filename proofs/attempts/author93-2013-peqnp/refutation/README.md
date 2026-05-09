# Maknickas (2013) - Refutation

## Why the Proof Fails

Maknickas's 2013 P=NP attempt contains a fundamental error: **LP (Linear Programming)
is conflated with ILP (Integer Linear Programming)**.

## The Fatal Error: LP/ILP Conflation

### The Claim

Maknickas claims that encoding SAT as a Linear Programming problem and solving it in
polynomial time proves SAT ∈ P, hence P = NP.

### The Problem

**LP and ILP are fundamentally different problems:**

| Aspect | LP (Linear Programming) | ILP (Integer Linear Programming) |
|--------|------------------------|----------------------------------|
| **Variables** | Real values (continuous) | Integer values (discrete) |
| **Complexity** | Polynomial time (P) | NP-complete |
| **SAT encoding** | May give fractional solutions | Correct encoding of SAT |
| **Example** | x = 0.5 is valid | x must be 0 or 1 |

### Why This Is Fatal

1. **SAT requires discrete solutions**: Boolean satisfiability needs assignments where
   each variable is either TRUE (1) or FALSE (0).
2. **LP allows fractional solutions**: The LP relaxation (variables in [0,1]) may
   have optimal solutions that are fractional (e.g., x = 0.5).
3. **Fractional solutions are not valid for SAT**: A fractional LP solution cannot
   be directly converted to a valid boolean assignment.
4. **Enforcing integrality makes it ILP**: If we require x_i ∈ {0, 1}, the problem
   becomes Integer Linear Programming, which is NP-complete.

## The Concrete Counterexample

Consider the formula: φ = (x ∨ y) ∧ (¬x ∨ ¬y)

**Satisfying boolean assignments** (there are two):
- x = 0, y = 1 (satisfies both clauses)
- x = 1, y = 0 (satisfies both clauses)

**The LP encoding**:
- Clause (x ∨ y): x + y ≥ 1
- Clause (¬x ∨ ¬y): (1 - x) + (1 - y) ≥ 1, i.e., x + y ≤ 1
- Variables: 0 ≤ x ≤ 1, 0 ≤ y ≤ 1

**A fractional LP solution**: x = 0.5, y = 0.5

This solution satisfies all LP constraints:
- x + y = 1.0 ≥ 1 ✓
- x + y = 1.0 ≤ 1 ✓
- 0 ≤ 0.5 ≤ 1 ✓

But x = 0.5 is **not** a valid boolean assignment! The LP solution does not
correspond to any boolean assignment for SAT.

## The Unavoidable Dilemma

Any attempt to encode SAT as LP faces an unavoidable dilemma:

### Option 1: Use integer constraints (x_i ∈ {0, 1})
- Result: **Integer Linear Programming (ILP)**
- Complexity: **NP-complete**
- This is not a polynomial-time algorithm

### Option 2: Omit integer constraints (x_i ∈ [0, 1])
- Result: **LP relaxation of SAT**
- LP solutions may be **fractional** (not valid boolean assignments)
- The LP solution does not necessarily correspond to a SAT solution

Neither option proves P = NP.

## Well-Known Background

This error is an instance of a well-known pitfall in computational complexity:

- **Theorem (Karp 1972)**: Every NP problem can be formulated as an ILP with
  polynomial-size encoding.
- **But**: ILP is itself NP-complete (Karp 1972).
- **Consequence**: Encoding NP problems as ILP does not give polynomial-time algorithms.

The error is recognizing LP and ILP as the same class of problems, when in fact
LP is in P but ILP is NP-complete.

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`fractional_satisfies_lp`**: The fractional solution (x=0.5, y=0.5) satisfies
   the LP constraints for the example formula.
2. **`half_not_boolean`**: The value 0.5 is not a valid boolean assignment.
3. **`maknickas_error_formalized`**: The dilemma that either integer constraints are
   needed (making it ILP) or fractional solutions arise (invalidating the approach).

## References

- **Maknickas, A.A.** (2013). "Linear Programming Formulation of Boolean Satisfiability
  Problem". In: Transactions on Engineering Technologies. LNEE, vol 275. Springer.
- **Cook, S.A.** (1971). "The complexity of theorem-proving procedures". STOC 1971.
- **Karp, R.M.** (1972). "Reducibility among combinatorial problems".
- **Khachiyan, L.G.** (1979). "A polynomial algorithm in linear programming".
- **Fiorini, S., et al.** (2015). "Exponential Lower Bounds for Polytopes in
  Combinatorial Optimization". Journal of the ACM.
- **Woeginger's List**: Entry #93 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
