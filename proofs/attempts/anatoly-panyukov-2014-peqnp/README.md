# Anatoly Panyukov (2014) - P=NP Attempt

**Attempt ID**: 101
**Author**: Anatoly Panyukov
**Year**: 2014
**Claim**: P=NP
**Paper**: [arXiv:1409.0375v5](http://arxiv.org/abs/1409.0375) - "Polynomial-Solvability of NP-class Problems"
**Status**: **INVALID** - Critical error in Theorem 1

---

## Summary

In September 2014, Anatoly Panyukov claimed to prove P=NP by constructing a polynomial-time algorithm for recognizing the cardinality of the "Hamiltonian complement" of a graph. The paper attempts to reduce this NP-complete problem to linear programming.

## Main Argument

### 1. Problem Definition

Panyukov introduces the **Hamiltonian complement** H(G) of a graph G = (V(G), E(G)) as the minimal cardinality set of edges H(G) ⊂ V(G) × V(G) such that the graph (V(G), E(G) ∪ H(G)) is Hamiltonian.

**Key observation**: If |H(G)| = 0, then G has a Hamiltonian circuit. Thus, computing |H(G)| solves the Hamiltonian circuit problem, which is NP-complete.

### 2. Formulation as Integer Linear Programming (ILP)

The paper formulates finding a Hamiltonian path as a Boolean optimization problem:

**Variables**: x^i_v ∈ {0,1} where x^i_v = 1 iff the i-th position in the path is vertex v

**Constraints**:
- D₁: Each position gets exactly one vertex: Σ_{v∈V(G)} x^i_v = 1 for all i
- D₂: Each vertex appears at most once: Σ^n_{i=1} x^i_v = 1 for all v
- D₃: Variables are binary: x^i_v ∈ {0,1}

**Objective**: Minimize the number of non-edges used:
```
F(x) = Σ^{n-1}_{i=1} Σ_{v,u: {v,u}∉E(G)} x^i_v · x^{i+1}_u
```

### 3. Linearization

Introduce auxiliary variables y^{(i,i+1)}_{(u,v)} = x^i_u · x^{i+1}_v to get an ILP (Problem 6).

### 4. LP Relaxation

Relax the ILP by dropping integrality constraints to get Problem (10) - a linear program that can be solved in polynomial time.

### 5. The Critical Claim (Theorem 1)

**Theorem 1** (Page 6): *"The set of optimal solutions of the relaxed problem (10) contains an integer solution."*

**Corollary**: If this were true, we could solve the Hamiltonian circuit problem by:
1. Solving the LP relaxation (10) in polynomial time
2. Obtaining an integer solution (by Theorem 1)
3. Checking if the objective value is 0

This would prove P=NP.

## The Error

### Location of the Error

**The error is in the proof of Theorem 1 (pages 6-8).**

### What Goes Wrong

The proof attempts to show Theorem 1 through a chain of equalities (16) involving several related optimization problems. The key steps are:

1. **Proposition 5** correctly shows that Problem (14) - a shortest path problem with only constraint D₁ - has totally unimodular constraint matrix and therefore integer optimal solutions.

2. **The Invalid Step**: The proof then attempts to show that the optimal solution of Problem (10) - which has BOTH constraints D₁ AND D₂ - must also be integer.

3. **The claim** (page 8): "The assumption S ⊄ D₂ ∩ D₃ contradicts to optimality of λ*" is stated without proof.

### Why The Proof Fails

The proof shows:
- ✓ Problem (14) has totally unimodular constraints (only D₁ + flow balance)
- ✓ Problem (14) has integer optimal solutions
- ✗ **GAP**: This does NOT imply Problem (10) has integer optimal solutions

**The crucial difference**: Problem (10) includes the surjectivity constraint D₂ (each vertex used exactly once), which Problem (14) lacks. Adding constraint D₂ destroys the total unimodularity.

### Why This Matters

**Integrality Gap**: For many graphs, the LP relaxation (10) has:
- Optimal value achieved only by fractional solutions
- Integer solutions with strictly worse (higher) objective values
- Positive "integrality gap" between LP and ILP optimal values

**What would be needed**: To prove Theorem 1, one would need to show that the constraint matrix of Problem (10) is totally unimodular, or use some other method to prove all optimal solutions are integral. The paper does neither.

### Specific Technical Issues

1. **Chain of equalities (16)**: The proof claims a chain of equalities ending with inequalities that allegedly must all be tight. The critical step assumes:
   ```
   min_{x∈D₁∩D₃, (x,y)∈M̃} F_W(λ*)(x,y) = min_{x∈D₁∩D₂, (x,y)∈M̃} F_W(λ*)(x,y)
   ```
   This is claimed to follow because the optimal solution must satisfy D₂, but this is circular reasoning - it assumes what needs to be proven.

2. **Constraint D₂ breaks structure**: The beautiful total unimodularity of the shortest path formulation is destroyed when adding the "each vertex exactly once" constraints.

3. **No counterexample consideration**: The paper never considers what happens if the LP optimal solution is fractional.

## Known Refutations

While no formal published refutation exists specifically for this paper, the claim contradicts:

1. **Decades of LP/ILP theory**: The integrality gap for Hamiltonian path ILP formulations is well-studied
2. **Empirical evidence**: LP relaxations of Hamiltonian path problems routinely have fractional optimal solutions
3. **The P≠NP consensus**: The overwhelming belief among complexity theorists

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the problem structure**: Formalizing graphs, Hamiltonian paths, and the ILP formulation
2. **Formalizing Theorem 1**: Stating precisely what the paper claims
3. **Identifying the gap**: Showing that the proof's key step (equation 16's tightness) is not justified
4. **Counterexample (sketch)**: Showing that LP relaxations can have fractional optimal solutions

## Implementation Structure

- **`rocq/PanyukovAttempt.v`**: Rocq formalization
- **`lean/PanyukovAttempt.lean`**: Lean 4 formalization
- **`isabelle/PanyukovAttempt.thy`**: Isabelle/HOL formalization

Each formalization:
1. Defines the Hamiltonian complement problem
2. Formalizes the ILP and LP formulations
3. States Theorem 1 as an axiom
4. Shows that Theorem 1 would imply P=NP
5. Identifies the proof gap
6. Notes that the proof is incomplete

## Key Lessons

### What the Paper Got Right

1. ✓ Correct formulation of Hamiltonian path as ILP
2. ✓ Valid linearization technique
3. ✓ Correct dual problem construction
4. ✓ Problem (14) does have totally unimodular constraints

### What the Paper Got Wrong

1. ✗ Theorem 1 is not proven (gap in proof)
2. ✗ Total unimodularity of (14) does not transfer to (10)
3. ✗ No consideration of integrality gaps
4. ✗ Invalid conclusion that P=NP

### Barriers Not Addressed

The paper does not address known barriers to proving P=NP:
- **Relativization** (Baker-Gill-Solovay, 1975)
- **Natural Proofs** (Razborov-Rudich, 1997)
- **Algebrization** (Aaronson-Wigderson, 2008)

The LP-based approach, if it worked, would need to overcome at least the relativization barrier.

## References

### The Original Paper

- Panyukov, A. (2018). "Polynomial-Solvability of NP-class Problems." arXiv:1409.0375v5 [cs.CC]
  - URL: https://arxiv.org/abs/1409.0375

### Background

- Cook, S. A. (1971). "The complexity of theorem proving procedures." *Proceedings of the 3rd ACM Symposium on Theory of Computing*, 151-158.
- Karp, R. M. (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, 85-104.
- Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.* W. H. Freeman.

### Relevant Theory

- **Integer Programming**: Theory of totally unimodular matrices and integrality gaps
- **Hamiltonian Path**: Known to be NP-complete (Karp, 1972)
- **LP Complexity**: Polynomial-time solvability (Khachiyan, 1979; Karmarkar, 1984)

## Woeginger's List

This attempt appears as **Entry #101** in Gerhard Woeginger's famous list of P vs NP attempts:
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Verification Status

- ✅ Rocq formalization: Compiles and identifies the gap
- ✅ Lean formalization: Type-checks and shows incompleteness
- ✅ Isabelle formalization: Verified and documents the error

## License

This formalization is provided for educational and research purposes under the repository's main license (The Unlicense).

---

**Navigation**: [↑ Back to Proofs](../../) | [Repository Root](../../../README.md) | [Issue #62](https://github.com/konard/p-vs-np/issues/62)
