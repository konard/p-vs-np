# Dr. Joachim Mertz (2005) - P=NP via MERLIN

**Attempt ID**: 26 (from Woeginger's list)
**Author**: Dr. Joachim Mertz
**Year**: 2005 (presented), 2007 (published)
**Claim**: P=NP
**Method**: Linear programming formulation of the Traveling Salesman Problem (TSP)
**Source**: Woeginger's P versus NP page - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

Dr. Joachim Mertz claimed to prove P=NP by presenting MERLIN (Merlin's Linear Integrated Network), a linear programming formulation of the Traveling Salesman Problem with O(n⁵) variables and O(n⁴) constraints. The approach was initially presented in 2005 and later published as "The Dragon War" in Applied Mathematics and Computation, Volume 186, Issue 1, March 1, 2007, pages 907-914.

## Main Argument

Mertz's approach follows this logical structure:

1. **TSP is NP-complete**: The Traveling Salesman Problem is a well-known NP-complete problem
2. **MERLIN formulation**: Define TSP as a linear program with:
   - O(n⁵) optimization variables
   - O(n⁴) linear constraints
3. **Linear programming is polynomial**: LP can be solved in polynomial time (e.g., using interior-point methods)
4. **Conclusion**: Since TSP can be formulated as LP with polynomial-sized input, TSP ∈ P, therefore P=NP

### MERLIN Formulation Details

The MERLIN approach uses the following structure:

**Graph Model:**
- Nodes labeled as (column, row) pairs
- Edges represented by optimization variables x_{i,j,k} where 0 ≤ x_{i,j,k} ≤ 1
- Routes start and end at station 0 (home office)

**Key Constraints:**
1. **Symmetry**: Visit each station exactly once (route must be symmetric)
2. **Consecutivity**: Use exactly one edge per position (route must be consecutive)
3. **Objective**: Minimize total route length

**Novel Mechanism:**
- Introduces "mirrors" to separate complementary sub-routes
- Enforces symmetry of each sub-route
- Claims to handle non-integer solutions by ensuring sub-routes are symmetric

## The Error

The fundamental flaw in Mertz's MERLIN approach is a classic mistake in computational complexity:

### Critical Error: Confusion Between LP Relaxation and Integer Programming

**The Problem:**

1. **LP vs ILP**: While linear programming (LP) can be solved in polynomial time, the TSP requires an **integer linear program** (ILP), not a continuous LP. ILP is known to be NP-complete.

2. **Fractional Solutions**: The MERLIN formulation produces a linear program whose solutions may be **fractional** (non-integer). For example, x_{i,j,k} = 0.5 means "use half of edge (i,j) at position k," which doesn't correspond to any valid TSP tour.

3. **LP Relaxation ≠ Original Problem**: Solving the LP relaxation of an NP-complete problem gives you a **lower bound** on the optimal solution, but not the solution itself. The gap between the LP relaxation and the integer solution is the core difficulty of NP-complete problems.

### Why "Tolerating Non-Integer Solutions" Doesn't Work

Mertz's approach claims to "tolerate non-integer results for a dedicated class of solutions (symmetric solutions)." However:

- A TSP tour must visit each city **exactly once** and use each edge **either 0 or 1 times** (binary decision)
- Fractional solutions like "use edge e with probability 0.3" don't represent valid tours
- Even if symmetric, a fractional solution doesn't give you a sequence of cities to visit
- The "mirror" mechanism doesn't resolve this fundamental issue—it just adds more constraints to the LP relaxation

### The Standard LP Relaxation of TSP

The LP relaxation of TSP has been well-studied:

```
minimize: Σ c_ij * x_ij
subject to:
  - Σ x_ij = 2 for all i (degree constraints)
  - x_ij ≥ 0 (non-negativity)
  - Additional constraints (subtour elimination, etc.)
```

This LP relaxation:
- Can be solved in polynomial time
- Gives a **lower bound** on optimal TSP tour length
- Often produces fractional solutions that must be "rounded" to integers
- **Rounding is NP-hard**—this is precisely where the difficulty lies!

### Why This Doesn't Prove P=NP

To actually prove P=NP via TSP, Mertz would need to show:

1. ✗ A polynomial-time algorithm that finds **integer** solutions (not fractional)
2. ✗ A proof that the LP relaxation always has an **integer optimal solution** (false—counterexamples exist)
3. ✗ A polynomial-time rounding procedure that converts fractional solutions to optimal integer solutions (this would itself solve P vs NP!)

None of these are provided. The MERLIN formulation only shows that:
- ✓ TSP can be **relaxed** to a polynomial-time solvable LP (known since the 1950s)
- ✓ The LP has O(n⁵) variables and O(n⁴) constraints (polynomial-sized, but very large)

## Formal Verification Goal

Our formalization in Coq, Lean, and Isabelle aims to:

1. **Define LP vs ILP**: Formalize the difference between linear programming and integer linear programming
2. **Model TSP**: Define the TSP problem and its requirement for integer solutions
3. **LP Relaxation**: Show that TSP can be relaxed to an LP
4. **Gap Identification**: Prove that solving the LP relaxation ≠ solving TSP
5. **Error Proof**: Formally verify that MERLIN's approach has a gap (fractional solutions don't solve TSP)

## Historical Context

This type of error is common in P vs NP attempts:

- **Confusion between relaxations and original problems**: Many attempts solve a relaxed version and claim it solves the original
- **LP/ILP confusion**: Linear programming is in P; integer linear programming is NP-complete
- **Rounding problem**: The difficulty of converting fractional solutions to integer solutions is precisely the hardness of NP-complete problems

Similar flawed approaches have been proposed for other NP-complete problems (SAT, graph coloring, etc.) with analogous errors.

## References

1. **Original Source**: Woeginger's P versus NP page, Entry #26
   - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

2. **Publication**: Joachim Mertz, "The Dragon War," Applied Mathematics and Computation, Volume 186, Issue 1, March 1, 2007, pp. 907-914
   - DOI: 10.1016/j.amc.2006.08.082
   - https://www.sciencedirect.com/science/article/abs/pii/S0096300306010137

3. **Original Website** (archived): http://www.merlins-world.de/
   - Note: Website no longer accessible as of 2025

4. **Background on TSP LP Relaxations**:
   - Held, M., & Karp, R. M. (1970). "The traveling-salesman problem and minimum spanning trees." Operations Research, 18(6), 1138-1162.
   - Dantzig, G., Fulkerson, R., & Johnson, S. (1954). "Solution of a large-scale traveling-salesman problem." Journal of the Operations Research Society of America, 2(4), 393-410.

5. **Integer Linear Programming Complexity**:
   - Karp, R. M. (1972). "Reducibility among combinatorial problems." Complexity of Computer Computations, 85-103.

## Formalization Structure

```
proofs/attempts/dr-joachim-mertz-2005-peqnp/
├── README.md (this file)
├── coq/
│   └── MertzMERLIN.v
├── lean/
│   └── MertzMERLIN.lean
└── isabelle/
    └── MertzMERLIN.thy
```

Each formalization:
- Defines TSP and its integer solution requirement
- Models linear programming and integer linear programming
- Formalizes the LP relaxation of TSP
- Proves that LP relaxation solutions may be fractional
- Shows the gap: fractional solutions ≠ valid TSP tours
- Concludes that MERLIN doesn't prove P=NP

## Lessons Learned

This attempt illustrates several important lessons:

1. **Polynomial-sized ≠ Polynomial-time**: Having polynomial constraints/variables doesn't automatically mean the problem is in P if integrality is required
2. **Relaxations are not solutions**: Solving a relaxed version of a problem doesn't solve the original problem
3. **LP ∈ P, ILP is NP-complete**: This distinction is crucial and well-established
4. **Rounding is hard**: Converting fractional solutions to integer solutions is often as hard as the original problem

## Status

- ✅ Folder structure created
- ✅ README with detailed description
- ⏳ Coq formalization (in progress)
- ⏳ Lean formalization (in progress)
- ⏳ Isabelle formalization (in progress)
- ✅ Error identified and documented

---

*Part of the P vs NP formal verification project - Testing all claimed proofs until errors are found.*
