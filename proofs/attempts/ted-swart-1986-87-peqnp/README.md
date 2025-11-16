# Ted Swart (1986/87) - P=NP via Linear Programming

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

**Attempt ID**: #1
**Author**: Ted Swart (University of Guelph)
**Year**: 1986/87
**Claim**: P = NP
**Status**: **REFUTED** by Yannakakis (1988/1991)

## Summary

In 1986/87, Ted Swart from the University of Guelph published a series of papers (some titled "P=NP") claiming to prove P=NP. His approach was based on providing polynomial-size linear programming (LP) formulations for the Hamiltonian cycle problem, which is known to be NP-hard.

**Swart's Argument**:
1. The Hamiltonian cycle problem is NP-hard
2. He claimed to construct a linear programming formulation of polynomial size for the Hamiltonian cycle problem
3. Linear programming is solvable in polynomial time (Khachiyan 1979, Karmarkar 1984)
4. Therefore, Hamiltonian cycle ∈ P
5. Since Hamiltonian cycle is NP-hard, this would imply P = NP

**Refutation**: In 1988, Mihalis Yannakakis presented a decisive refutation at STOC 1988 (journal version in JCSS 1991), proving that any *symmetric* linear program for the Traveling Salesman Problem (TSP) must have exponential size. This closed the discussion on Swart's approach.

## The Main Argument

### Swart's Approach

Swart attempted to formulate the Hamiltonian cycle problem as a linear program with:
- Variables: A polynomial number (reportedly n^8 to n^10, where n is the number of vertices)
- Constraints: Linear inequalities defining a polytope
- Objective: Find a feasible solution in the polytope

The key insight Swart tried to exploit: If the Hamiltonian cycle problem can be expressed as a polynomial-size LP, and LP is in P, then Hamiltonian cycle is in P, which would prove P=NP since Hamiltonian cycle is NP-complete.

### Why This Seemed Plausible

1. **Linear Programming is in P**: The ellipsoid method (Khachiyan, 1979) and interior point methods (Karmarkar, 1984) can solve linear programs in polynomial time
2. **Many Problems Have LP Formulations**: Integer linear programming (ILP) can express many combinatorial problems
3. **Relaxations Often Work Well**: In practice, LP relaxations of ILP problems often give good approximate solutions

## The Error in Swart's Proof

### The Fatal Flaw: Confusing LP with ILP

The critical error in Swart's approach is the confusion between:
- **Linear Programming (LP)**: Variables can be real numbers
- **Integer Linear Programming (ILP)**: Variables must be integers

**Key distinction**:
- LP is solvable in polynomial time
- ILP is NP-complete

### What Swart Actually Showed (at best)

If Swart had a correct formulation, it would be an *integer* linear program, not a pure linear program. The Hamiltonian cycle problem naturally requires discrete choices (edge is in cycle or not), which requires integer constraints.

### Extended Formulations and Symmetry

Even if one considers LP *extended formulations* (where the polytope projects onto the convex hull of Hamiltonian cycles), Yannakakis proved a fundamental barrier:

**Yannakakis's Theorem (1988/1991)**: Any *symmetric* extended formulation for the Traveling Salesman Problem requires exponential size.

**Definition**: An LP is *symmetric* if every permutation of vertices can be extended to a permutation of all variables that preserves the constraints.

Since natural formulations of graph problems are symmetric (they don't distinguish between vertices arbitrarily), this result showed that Swart's approach was fundamentally blocked.

### The Full Story: Fiorini et al. (2012)

The question remained: What about *non-symmetric* extended formulations?

In 2012, Fiorini, Massar, Pokutta, Tiwary, and de Wolf proved that **no** polynomial-size extended formulation exists for TSP, symmetric or not. This completely ruled out any LP-based approach to proving P=NP.

## Known Refutation

### Yannakakis (1988): "Expressing Combinatorial Optimization Problems by Linear Programs"

**Conference**: STOC 1988, pp. 223-228
**Journal**: Journal of Computer and System Sciences, Vol. 43, 1991, pp. 441-466

**Main Result**: Yannakakis proved that expressing the Traveling Salesman Problem (and by extension, Hamiltonian cycle) using a symmetric linear program requires exponential size.

**Technique**: Yannakakis used non-negative matrix factorization to show that the "slack matrix" of any symmetric extended formulation must have exponential non-negative rank.

**Implication**: Any natural, symmetric LP formulation for Hamiltonian problems cannot be polynomial-sized.

### Fiorini et al. (2012): Beyond Symmetry

**Citation**: "Exponential Lower Bounds for Polytopes in Combinatorial Optimization"
**Journal**: Journal of the ACM, Vol. 62, No. 2, 2015 (conference version STOC 2012)
**Award**: Gödel Prize 2023

**Main Result**: The TSP polytope has no polynomial-size extended formulation, even allowing non-symmetric formulations.

**Implication**: Even creative, asymmetric LP formulations cannot avoid exponential size for TSP.

## Formal Verification

This directory contains formal proofs in three proof assistants that capture the logical error in Swart's argument:

### Structure of Formalizations

Each formalization implements:

1. **Definitions**:
   - Linear Program (LP): Real-valued variables
   - Integer Linear Program (ILP): Integer-valued variables
   - Polynomial size: Number of variables/constraints is polynomial in input size
   - Hamiltonian cycle problem

2. **Correct Statements**:
   - LP ∈ P (polynomial-time solvable)
   - Hamiltonian cycle ∈ NP
   - Hamiltonian cycle is NP-hard

3. **The Logical Gap**:
   - Swart's claim: Hamiltonian cycle has polynomial-size *LP* formulation
   - Reality: Hamiltonian cycle has polynomial-size *ILP* formulation (trivial)
   - The gap: LP formulation ≠ ILP formulation for discrete problems

4. **Yannakakis's Barrier**:
   - Even symmetric extended formulations require exponential size
   - Natural formulations are symmetric
   - Therefore, Swart's approach cannot work

### Files

```
proofs/attempts/ted-swart-1986-87-peqnp/
├── README.md                          # This file
├── coq/
│   └── TedSwart1986.v                # Coq formalization
├── lean/
│   └── TedSwart1986.lean             # Lean 4 formalization
└── isabelle/
    └── TedSwart1986.thy              # Isabelle/HOL formalization
```

## Why This Attempt is Important

### Educational Value

1. **Common Mistake**: Highlights the critical difference between LP and ILP
2. **Extended Formulations**: Demonstrates the power and limits of LP relaxations
3. **Symmetry**: Shows how symmetry constraints can impose fundamental limitations
4. **Proof Barriers**: Illustrates that some approaches are provably doomed

### Historical Significance

1. **Motivated Deep Research**: Yannakakis's refutation led to decades of research on extended formulations
2. **Gödel Prize**: The line of research culminated in a Gödel Prize-winning result (Fiorini et al., 2023)
3. **Proof Technique**: Introduced non-negative rank as a tool in complexity theory

### Complexity Theory Lessons

1. **P vs NP Cannot Be Solved by LP Methods**: Fiorini et al. showed this definitively
2. **Natural Proofs Barrier**: Related to Razborov-Rudich's natural proofs barrier
3. **Practical Implications**: Explains why LP relaxations, while useful in practice, cannot resolve P vs NP

## References

### Primary Sources

1. **Swart, E.R.** (1986/87). *P=NP* (series of papers). University of Guelph.

2. **Yannakakis, M.** (1988). "Expressing Combinatorial Optimization Problems by Linear Programs." *Proceedings of STOC 1988*, pp. 223-228.

3. **Yannakakis, M.** (1991). "Expressing Combinatorial Optimization Problems by Linear Programs." *Journal of Computer and System Sciences*, Vol. 43, pp. 441-466.

4. **Fiorini, S., Massar, S., Pokutta, S., Tiwary, H. R., & de Wolf, R.** (2012). "Linear vs. Semidefinite Extended Formulations: Exponential Separation and Strong Lower Bounds." *Proceedings of STOC 2012*, pp. 95-106.

5. **Fiorini, S., Massar, S., Pokutta, S., Tiwary, H. R., & de Wolf, R.** (2015). "Exponential Lower Bounds for Polytopes in Combinatorial Optimization." *Journal of the ACM*, Vol. 62, No. 2, Article 17.

### Background Reading

6. **Khachiyan, L.G.** (1979). "A Polynomial Algorithm in Linear Programming." *Soviet Mathematics Doklady*, Vol. 20, pp. 191-194.

7. **Karmarkar, N.** (1984). "A New Polynomial-time Algorithm for Linear Programming." *Combinatorica*, Vol. 4, pp. 373-395.

8. **Woeginger, G.J.** "The P-versus-NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #1)

9. **Pokutta, S.** (2012). "On linear programming formulations for the TSP polytope." Blog post. https://spokutta.wordpress.com/2012/01/05/1311/

## Verification Status

- ✅ **Lean 4**: Definitions compile, logical gap formalized
- ✅ **Coq**: Definitions compile, error identified formally
- ✅ **Isabelle/HOL**: Definitions compile, refutation structure formalized

## License

This formalization is part of the p-vs-np repository and follows the repository's [LICENSE](../../../LICENSE).

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Parent Issue #44: Test All Attempts](https://github.com/konard/p-vs-np/issues/44) | [This Issue #58](https://github.com/konard/p-vs-np/issues/58)
