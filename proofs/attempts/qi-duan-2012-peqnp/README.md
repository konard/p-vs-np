# Qi Duan (2012) - P=NP Proof Attempt

**Attempt ID**: 89
**Author**: Wen-Qi Duan
**Year**: July 2012
**Claim**: P = NP
**Status**: Refuted (listed on Woeginger's list of flawed P vs NP proofs)
**Source**: [arXiv:1208.0542](http://arxiv.org/abs/1208.0542)

## Summary

In July 2012, Wen-Qi Duan claimed to prove P=NP through a constructive algorithm. The paper "A Constructive Algorithm to Prove P=NP" proposes solving the undirected Hamiltonian cycle problem in polynomial time by:

1. Reducing the Hamiltonian cycle problem to a Traveling Salesman Problem (TSP) with edge costs restricted to 0 or 1
2. Developing an algorithm to compute the optimal tour through a "growth process"
3. Invoking the Cook-Levin theorem to conclude P=NP

This attempt appears as entry #93 on Gerhard Woeginger's comprehensive list of flawed P vs NP proof attempts.

## Main Argument

### The Reduction Strategy

The paper claims to reduce the undirected Hamiltonian cycle problem (which is NP-complete) to a special case of TSP where all edge costs are either 0 or 1. This reduction is standard and correct:

- Given a graph G = (V, E), create a complete graph with the same vertices
- For edges in E, assign cost 0
- For edges not in E, assign cost 1
- A tour of cost 0 exists if and only if G has a Hamiltonian cycle

**Note**: This reduction is well-known and unproblematic. The issue lies in the claimed algorithm.

### The Growth Process Algorithm

Duan proposes a "growth process" algorithm with the following steps:

1. **Initialize**: Start with an optimal tour on 4 vertices
2. **Iterate**: Incrementally add one new vertex at a time to the current tour
3. **Maintain Optimality**: At each step, insert the new vertex in a way that produces an optimal tour for the expanded vertex set
4. **Terminate**: Continue until all vertices are included

The paper claims this process:
- Always produces an optimal tour at each step
- Runs in polynomial time
- Solves the TSP instance (and thus the Hamiltonian cycle problem) in polynomial time

### The Claimed Conclusion

By the Cook-Levin theorem, if any NP-complete problem (such as Hamiltonian cycle) can be solved in polynomial time, then P = NP. Therefore, Duan claims to have proved P = NP constructively.

## The Error

While the paper does not provide sufficient algorithmic details for a complete formal analysis, the fundamental flaw lies in the **maintenance of optimality claim** during the growth process:

### Critical Issue: The Greedy Insertion Fallacy

The paper's algorithm assumes that by greedily inserting vertices one at a time while maintaining local optimality, one can achieve global optimality for TSP. This is a well-known fallacy in combinatorial optimization:

1. **No Polynomial-Time Optimal Insertion**: There is no known polynomial-time method to insert a new vertex into a partial tour while guaranteeing that the resulting expanded tour is optimal among all tours on the expanded vertex set.

2. **Optimal Substructure Violation**: TSP does not have the optimal substructure property required for dynamic programming or greedy algorithms to work. An optimal tour on n vertices does not necessarily contain an optimal tour on n-1 vertices as a subpath.

3. **Counterexample**: Consider a simple case:
   - Optimal 4-vertex tour: A → B → C → D → A
   - Add vertex E
   - The optimal 5-vertex tour might be: A → E → B → D → C → A
   - This might not be obtainable by inserting E into the 4-vertex tour

4. **The Real Complexity**: Finding the optimal insertion position for a new vertex requires considering all possible positions and evaluating the resulting tour costs, but this doesn't guarantee global optimality. More fundamentally, even if we could find the best insertion position in polynomial time, the resulting tour might not be globally optimal because TSP lacks the optimal substructure property.

### Why This Matters

The claim that "incrementally adding vertices while maintaining optimality" yields a polynomial-time algorithm is precisely what makes TSP hard. If such an algorithm existed, we would have already solved P vs NP decades ago when TSP was first studied.

### Missing Details

The paper lacks:
- **Rigorous proof** that the growth process maintains optimality
- **Detailed algorithm** for the insertion step
- **Complexity analysis** showing polynomial time bound
- **Proof of correctness** for the overall approach
- **Counterexample analysis** explaining why known TSP hardness results don't apply

## Formalization Strategy

Our formalization in Rocq, Lean, and Isabelle will:

1. **Define the problem**: Hamiltonian cycle, TSP, and the 0-1 cost reduction
2. **Formalize the algorithm**: Express the growth process as precisely as possible given the limited details
3. **Identify the gap**: Explicitly mark the unproven claim about optimality preservation
4. **Show the challenge**: Demonstrate why proving this claim is equivalent to solving P vs NP

The proof obligations that cannot be fulfilled will clearly show where the argument breaks down.

## References

- **Original Paper**: Wen-Qi Duan, "A Constructive Algorithm to Prove P=NP", arXiv:1208.0542, July 2012
- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #93)
- **TSP Hardness**: Garey & Johnson, "Computers and Intractability", 1979
- **Hamiltonian Cycle NP-Completeness**: Karp's 21 NP-complete problems, 1972

## Related Work

This attempt is similar to other flawed approaches that:
- Assume greedy or local optimization strategies work for NP-complete problems
- Lack rigorous proofs of optimality preservation
- Underestimate the difficulty of maintaining global optimality in incremental algorithms
- Confuse local improvements with global optimality

## Educational Value

This formalization demonstrates:
- How insufficient algorithmic details make verification impossible
- Why optimal substructure is crucial for dynamic programming
- The difference between local and global optimality
- How unproven lemmas can hide the core difficulty of a problem

## File Structure

```
proofs/attempts/qi-duan-2012-peqnp/
├── README.md (this file)
├── rocq/
│   └── QiDuan2012.v
├── lean/
│   └── QiDuan2012.lean
└── isabelle/
    └── QiDuan2012.thy
```

Each formalization file contains:
- Definition of Hamiltonian cycle and TSP problems
- The 0-1 cost reduction (correct part)
- Formalization of the growth process algorithm
- Explicit gaps in the proof (marked with `Admitted`/`sorry`/`oops`)
- Commentary on why these gaps cannot be filled without solving P vs NP

## Verification Status

All formalizations are designed to:
- ✅ Type-check and compile successfully
- ✅ Accurately represent the claimed algorithm
- ✅ Explicitly mark unproven claims
- ❌ Do NOT claim to prove P = NP (because the original proof is flawed)

The use of `Admitted` (Rocq), `sorry` (Lean), and `oops` (Isabelle) honestly represents our inability to complete the proof, which reflects the actual flaw in Duan's argument.
