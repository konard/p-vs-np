# Formalization: Hanlin Liu (2014) - P=NP

**Attempt ID**: 96
**Author**: Hanlin Liu
**Year**: 2014
**Claim**: P=NP
**Paper**: "A Algorithm for the Hamilton Circuit Problem"
**Source**: http://arxiv.org/abs/1401.6423
**Listed in**: Woeginger's P vs NP page (Entry #96)

## Summary

In January 2014, Hanlin Liu published a paper claiming to establish P=NP by constructing a polynomial-time algorithm for the Hamiltonian circuit problem with time complexity O(|V|^9).

**Important Note**: This paper has been **withdrawn by the author** with the following comment:
> "Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt."

This self-retraction makes the paper particularly interesting for formalization, as it demonstrates how incomplete algorithms can fail to cover all graph instances.

## Main Argument

### The Approach

The paper attempts to solve the Hamiltonian Circuit Problem (HCP) for a graph G=(V,E) in polynomial time O(|V|^9). The general approach for such claims typically involves:

1. **Graph Decomposition**: Attempting to decompose the graph into manageable substructures
2. **Path Extension**: Building candidate Hamiltonian paths incrementally
3. **Backtracking Avoidance**: Claiming to avoid exponential backtracking through clever pruning

### Common Patterns in Failed Attempts

Since the original PDF is no longer available (withdrawn from arXiv), we analyze based on common patterns in similar attempts to solve Hamiltonian circuit in polynomial time:

1. **Greedy Path Construction**: Build paths by always choosing the "best" next vertex
   - **Flaw**: Local optimality doesn't guarantee global Hamiltonian path existence

2. **Degree-based Heuristics**: Use vertex degrees to guide path construction
   - **Flaw**: Degree constraints are necessary but not sufficient for Hamiltonicity

3. **Connectivity Arguments**: Claim that certain connectivity properties ensure Hamiltonicity
   - **Flaw**: Connectivity doesn't imply Hamiltonicity (e.g., Petersen graph is 3-regular, 3-connected, but not Hamiltonian)

4. **Incomplete Case Analysis**: Algorithm works for special graph classes but not all graphs
   - **Flaw**: This is exactly what the author admitted - "it can not cover all cases"

## The Critical Error

### Primary Flaw: Incomplete Coverage

As admitted by the author, the algorithm fails to cover all cases of the Hamiltonian circuit problem. This is a fundamental issue because:

1. **NP-completeness**: The Hamiltonian circuit problem is NP-complete (Karp, 1972)
2. **Reduction hardness**: Any polynomial-time algorithm must handle ALL instances
3. **Worst-case complexity**: A single class of uncovered instances invalidates the P=NP claim

### Likely Failure Modes

Based on common patterns in similar attempts, the algorithm likely fails on:

1. **Sparse graphs**: Graphs with few edges where path choices are constrained
2. **Non-Hamiltonian graphs**: Graphs with no Hamiltonian cycle (algorithm may not terminate or give false positives)
3. **Near-Hamiltonian graphs**: Graphs that are "almost" Hamiltonian but have subtle obstructions
4. **Counter-examples**: Specific graph constructions designed to exploit greedy/local approaches

### Why O(|V|^9) is Suspicious

The claimed complexity O(|V|^9) is polynomial but extremely high. This suggests:
- The algorithm may be enumerating many possible path configurations
- Higher polynomial degrees often indicate incomplete pruning of the search space
- True polynomial algorithms for such problems typically have lower degrees

## Known Counterexamples

### The Petersen Graph

A classic counterexample for many Hamiltonian circuit heuristics:
- 10 vertices, 15 edges
- 3-regular (every vertex has degree 3)
- 3-connected (remains connected after removing any 2 vertices)
- **NOT Hamiltonian** despite appearing highly regular

### Hypohamiltonian Graphs

Graphs that are not Hamiltonian, but become Hamiltonian when any single vertex is removed:
- Demonstrate subtle obstructions to Hamiltonicity
- Often defeat local/greedy approaches

## Formalization Goal

Our formalization will:

1. **Define Hamiltonian cycles formally**: Precise definition in proof assistants
2. **Model the algorithm structure**: Represent typical greedy path construction approaches
3. **Construct counterexamples**: Provide specific graphs where greedy approaches fail
4. **Prove incompleteness**: Show that polynomial-time coverage of all cases is not achieved

## Implementation Structure

### Coq Formalization (`coq/`)
- Definitions of graphs, paths, and Hamiltonian cycles
- Greedy path construction model
- Counterexample construction (non-Hamiltonian regular graphs)
- Proof that greedy approaches have failure cases

### Lean Formalization (`lean/`)
- Type-safe graph structures
- Path extension algorithms
- Petersen graph as counterexample
- Proof of incompleteness for greedy strategies

### Isabelle Formalization (`isabelle/`)
- Higher-order logic representation
- Graph theory foundations
- Formal verification of counterexamples
- Gap demonstration

## References

### Primary Source
- **Liu, H.** (2014). "A Algorithm for the Hamilton Circuit Problem." arXiv:1401.6423. http://arxiv.org/abs/1401.6423 (Withdrawn)

### Classical Results
- **Karp, R. M.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*
- **Holton, D. A., & Sheehan, J.** (1993). *The Petersen Graph*. Cambridge University Press
- **Garey, M. R., & Johnson, D. S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*

### Woeginger's List
- **Woeginger, G. J.** "The P versus NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Status

- [x] Problem structure identified
- [x] Critical error located: Incomplete case coverage (author-confirmed)
- [x] Formal verification in progress
- [x] Counterexamples constructed

## Conclusion

The Hanlin Liu (2014) proof attempt was self-retracted by the author, who acknowledged that the algorithm "can not cover all cases of hamilton circuit problem." This is a classic failure mode for P=NP proof attempts: an algorithm that works on many or most instances but fails on certain graph classes. Since NP-completeness requires solving ALL instances in polynomial time, any uncovered cases invalidate the P=NP claim.

The formalization demonstrates this gap by:
1. Modeling the general structure of greedy Hamiltonian path algorithms
2. Constructing counterexample graphs (Petersen graph, hypohamiltonian graphs)
3. Proving that these counterexamples cannot be handled by local/greedy approaches

---

**Navigation:** [Back to Attempts](../) | [Repository Root](../../../README.md)
