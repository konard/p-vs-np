# Sergey Gubin (2010) - P=NP via ATSP Polytope Formulation

**Attempt ID**: 66 (from Woeginger's list)
**Author**: Sergey Gubin
**Year**: 2010
**Claim**: P = NP
**Status**: Refuted

**Formalization status:** The [refutation audit](refutation/README.md) now
checks a six-vertex counterexample against Gubin's actual equations (1.8) and
(1.9) in both Lean and Rocq. The earlier abstract refutations were withdrawn.

## Summary

In August 2010, Sergey Gubin published a paper titled "Complementary to Yannakakis' Theorem" claiming to prove P = NP. The work was presented at the 22nd MCCCC conference in Las Vegas in 2008 and later published in Volume 74 of *The Journal of Combinatorial Mathematics and Combinatorial Computing* (pages 313-321).

Gubin's approach was similar to other linear programming-based attempts: he claimed that the Asymmetric Traveling Salesman Problem (ATSP) polytope can be expressed by an asymmetric linear program of polynomial size. Since linear programming problems can be solved in polynomial time, and ATSP is NP-complete, this would imply P = NP.

## Main Argument

### The Approach

1. **ATSP Polytope**: Focus on the polytope associated with the Asymmetric Traveling Salesman Problem
2. **Polynomial-Sized LP**: Construct a linear programming formulation of polynomial size for the ATSP polytope
3. **Reference to Yannakakis**: Position the work as "complementary" to Yannakakis' theorem
4. **LP Solvability**: Leverage the fact that LP problems can be solved in polynomial time
5. **Claimed Implication**: If ATSP (an NP-complete problem) can be formulated and solved as polynomial-sized LP, then P = NP

### Connection to Yannakakis' Theorem

Yannakakis' theorem (1991) is a fundamental result in polyhedral combinatorics stating that the Traveling Salesman Problem polytope cannot be expressed via a symmetric extended formulation of polynomial size. This was a significant negative result showing limitations of certain approaches to solving NP-complete problems via linear programming.

Gubin's claim to be "complementary" to Yannakakis suggests:
- He may have attempted an **asymmetric** formulation (as opposed to symmetric)
- Or he may have claimed to work around Yannakakis' limitations in some other way

However, Yannakakis' result is a fundamental barrier, and circumventing it requires extraordinary proof.

## The Error

### Fundamental Issues with the Approach

**The Core Problem**: Like other LP-based P = NP attempts, this approach faces the fundamental gap between:
- **Linear Programming (LP)**: Can be solved in polynomial time, but solutions may be fractional
- **Integer Linear Programming (ILP)**: NP-complete, solutions are integral

**Why This Matters**:
1. The TSP/ATSP requires integer solutions (tours are discrete structures)
2. An LP formulation naturally allows fractional solutions
3. For the approach to work, the LP projection and objective must recover valid tours and their costs
4. Integrality of every extended coordinate would be one strong sufficient condition, but is not necessary for every extended formulation

### Failure of Exact Correspondence

The new formal counterexample uses two disjoint directed 3-cycles. The paper's
equations (1.8) and (1.9) have an explicit rational feasible point for this
graph, yet the graph has no Hamiltonian tour. Thus its Theorem 1.2, which
identifies that feasible region with the convex hull of solution grids, fails.

This failed correspondence allows feasible LP points that do not represent
tours. The example proves this directly for the paper's constraints.

### Refutation

The [paper counterexample](refutation/README.md) is checked directly in Lean
and Rocq. It is an independent six-vertex witness, not a formalization of
Hofman's or Rizzi's historical counterexample. Hofman's
[2006 report](https://arxiv.org/abs/cs/0610125) states that its own examples
also apply to Gubin's work.

## Historical Context

### Yannakakis' Theorem Background

**Yannakakis (1991)**: Showed that the TSP polytope has no symmetric polynomial-size extended formulation. This result:
- Closed off one natural approach to solving TSP via LP
- Established fundamental limits on polyhedral methods
- Is a cornerstone result in combinatorial optimization

### The LP vs ILP Gap

This is a well-understood barrier in complexity theory:
- **LP (Linear Programming)**: In P - solvable via ellipsoid method, interior point methods
- **ILP (Integer Linear Programming)**: NP-complete - fundamentally harder
- **The Gap**: Converting continuous optimization to discrete optimization is the hard part

Many attempted P = NP proofs try to bridge this gap by claiming:
- "My LP formulation has integral extreme points"
- "The polytope structure ensures integrality"
- "The formulation is 'complementary' to known limitations"

But proving such claims requires rigorous mathematical proof, which is typically where these attempts fail.

## Similar Attempts

### Related LP-Based P=NP Claims

1. **Moustapha Diaby (2004)**: Claimed polynomial-sized LP formulation of TSP
   - Refuted by Hofman (2006, 2025) with counter-examples
   - See: `proofs/attempts/moustapha-diaby-2004-peqnp/`

2. **Other ATSP/TSP LP attempts**: Multiple researchers have tried similar approaches
   - All face the same fundamental issue: the LP/ILP gap
   - Counterexamples can expose invalid projections or incorrect objective values

### Why These Approaches Are Tempting

The strategy is appealing because:
- LP formulations of TSP/ATSP do exist
- LP can be solved efficiently
- The connection seems "almost there"
- Small variations (symmetric vs asymmetric, different constraints) seem like they might work

But the fundamental barrier remains: **integrality is hard**.

## Formalization Status

The forward files specify the required tour/vertex correspondence without
asserting it. The original audit files prove two illustrative LP countermodels.
The new paper counterexample files transcribe equations (1.8) and (1.9) for
six vertices and prove that they admit a feasible point for a graph without a
Hamiltonian tour. They do not formalize the paper's symmetry or complexity
claims, which are unnecessary for this refutation of Theorem 1.2.

## References

### Primary Sources

- **Original Paper**: Gubin, S. (2010). "Complementary to Yannakakis' Theorem"
  - *The Journal of Combinatorial Mathematics and Combinatorial Computing*, Volume 74, pages 313-321
  - Also appeared on arXiv: https://arxiv.org/abs/cs/0610042
  - Conference presentation: 22nd MCCCC conference, Las Vegas, 2008

### Refutations

- **Radoslaw Hofman (2006)**: [Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem](https://arxiv.org/abs/cs/0610125)
  - Its abstract explicitly includes Gubin's paper among the affected works.
- **Romeo Rizzi (2011)**: Refutation published in January 2011
  - Specific publication details not widely available
  - Listed in Woeginger's P vs NP page as refuting Gubin's claim

### Related Work

- **Yannakakis (1991)**: "Expressing combinatorial optimization problems by linear programs"
  - *Journal of Computer and System Sciences*, 43(3), 441-466
  - DOI: 10.1016/0022-0000(91)90024-Y
  - Fundamental result on limitations of symmetric LP formulations

- **Diaby (2004-2006)**: Similar LP-based TSP approach
  - arXiv:cs/0609005
  - http://www.business.uconn.edu/users/mdiaby/tsplp/

- **Hofman (2006)**: "Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem"
  - arXiv:cs/0610125
  - Counter-examples to LP-based approaches

### Context

- **Woeginger's List**: Entry #66
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Comprehensive list of P vs NP attempts with status

## Key Lessons

1. **The LP/ILP Distinction**: The gap between continuous and discrete optimization is fundamental to computational complexity

2. **Exactness Needs Proof**: A polynomial size count does not establish that an LP solves the original optimization problem

3. **Yannakakis' Barrier**: Fundamental limitations exist on polyhedral approaches to NP-complete problems

4. **"Complementary" Doesn't Mean "Circumvents"**: Being complementary to a negative result doesn't automatically mean you've found a workaround

5. **Proof Obligations**: Claiming a formulation has special properties (like integrality) requires rigorous proof, not just construction

6. **Common Pattern**: Many P = NP attempts follow similar structures and fail at similar points

## Technical Details

### The ATSP Problem

The Asymmetric Traveling Salesman Problem:
- **Input**: A directed graph with edge weights
- **Question**: Find a minimum-weight Hamiltonian cycle
- **Asymmetry**: The weight from vertex i to j may differ from j to i

### Why ATSP vs TSP?

- **TSP**: Symmetric - edge weights are the same in both directions
- **ATSP**: Asymmetric - allows different weights for different directions
- **Complexity**: Both are NP-complete
- **Yannakakis' Result**: Applies to symmetric formulations
- **Gubin's Angle**: Focus on asymmetric formulations as potentially avoiding the barrier

However, asymmetry alone doesn't solve the fundamental integrality problem.

## See Also

- [Moustapha Diaby's TSP Attempt](../moustapha-diaby-2004-peqnp/) - Similar LP-based approach
- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches
- [Repository README](../../../README.md) - Overview of the P vs NP problem
