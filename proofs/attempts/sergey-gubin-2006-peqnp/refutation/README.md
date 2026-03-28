# Sergey Gubin (2006) - Refutation

## Why the Proof Fails

Gubin's 2006 P=NP attempt proposed two approaches, both of which contain fatal errors:

1. **ATSP/LP Approach**: Non-integral extreme points exist (Hofman 2006)
2. **SAT Reduction Approach**: Exponential blowup in clause count (Christopher et al. 2008)

## Error 1: Non-Integral Extreme Points (Hofman 2006)

### The Claim

Gubin claimed that all extreme points of his LP formulation are integral (0-1 valued), and that these integral extreme points correspond exactly to valid ATSP tours.

### The Counter-Example

Hofman (arXiv:cs/0610125) demonstrated that Gubin's LP formulation has **fractional extreme points** - vertices of the polytope that are not 0-1 valued.

**Key Finding**: There exist extreme points where:
- Variable values are fractional (e.g., x_{ij} = 0.5)
- These points do not correspond to any valid tour
- Optimizing over the LP may return such fractional points

### Why This Is Fatal

If the LP has non-integral extreme points:
1. The LP optimal solution may be fractional
2. A fractional solution does not define a valid tour
3. Rounding may not preserve optimality
4. The correspondence between LP solutions and tours breaks down

Therefore, solving the LP does not directly solve ATSP.

## Error 2: Exponential Blowup (Christopher, Huo, Jacobs 2008)

### The Claim

Gubin claimed that any SAT instance can be reduced to a 2-SAT instance in polynomial time, preserving satisfiability.

### The Counter-Example

Christopher, Huo, and Jacobs (arXiv:0804.2699) showed that any correct reduction from general SAT to 2-SAT must have **exponential blowup**.

**Key Finding**: Converting a k-clause (k ≥ 3) to equivalent 2-clauses requires:
- Either exponentially many clauses
- Or exponentially many auxiliary variables
- In either case, the reduction is not polynomial

### Why This Is Fatal

Since 2-SAT has strictly less expressive power than 3-SAT:
1. No polynomial-size 2-CNF can capture arbitrary 3-CNF satisfiability
2. Any correct transformation must be exponential
3. Using the 2-SAT solver on the transformed formula takes exponential time
4. The approach does not provide a polynomial-time algorithm

## Error 3: Missing Rigorous Proofs

Both of Gubin's approaches suffer from a common flaw: **critical claims are asserted without proof**.

### ATSP Approach

- Claimed: "All extreme points are integral"
- Missing: Proof that subtour elimination constraints maintain integrality
- Reality: Standard LP relaxations of TSP are known to have fractional extreme points

### SAT Approach

- Claimed: "Reduction has polynomial blowup"
- Missing: Proof of polynomial bound on output size
- Reality: Exponential blowup is unavoidable (unless P = NP)

## Mathematical Foundations

### Why LP Integrality Is Hard

The LP relaxation of an integer program has integral extreme points if and only if the constraint matrix is **totally unimodular** (or satisfies similar structural properties).

General TSP constraints do NOT satisfy these conditions:
- Subtour elimination constraints create complex interdependencies
- The TSP polytope is not integral for LP relaxations of polynomial size

### Why SAT to 2-SAT Is Hard

2-SAT and 3-SAT have fundamentally different complexity:
- 2-SAT is in P (can be solved by unit propagation and SCC analysis)
- 3-SAT is NP-complete (Cook-Levin theorem)

Any polynomial reduction from 3-SAT to 2-SAT would imply P = NP, which contradicts the widely-believed separation.

## The Dilemma

For any LP-based approach to prove P = NP:

### Option 1: LP is too weak
If the LP formulation is genuinely polynomial-sized and tractable, it likely does not capture the full NP-hard structure.

### Option 2: LP captures NP
If the LP truly captures an NP-hard problem, then either:
- The LP has exponentially many constraints, or
- The integrality gap exists (fractional solutions)

There is no middle ground that both captures NP-hardness and maintains polynomial tractability.

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`not_all_extreme_points_integral`**: Hofman's counter-example breaks the integrality assumption
2. **`no_polynomial_SAT_to_2SAT_reduction`**: Christopher et al.'s result shows exponential blowup
3. **`gubin_both_approaches_fail`**: Combined proof that neither approach works

## References

- **Hofman, P.** (2006). "Report on article: P=NP". arXiv:cs/0610125
- **Christopher, I., Huo, D., & Jacobs, B.** (2008). "Critique of Gubin's SAT Solver". arXiv:0804.2699
- **Cook, S. A.** (1971). "The complexity of theorem-proving procedures"
- **Karmarkar, N.** (1984). "A new polynomial-time algorithm for linear programming"
