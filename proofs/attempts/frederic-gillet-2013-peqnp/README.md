# Frederic Gillet (2013) - P=NP Attempt

**Attempt ID**: 95 (from Woeginger's list)
**Author**: Frederic Gillet
**Year**: 2013
**Claim**: P=NP
**Paper**: "Solving 3-SAT and 3-dimensional matching in polynomial time"
**arXiv**: [1310.1971](https://arxiv.org/abs/1310.1971) (withdrawn)
**Status**: **Retracted by author**

## Summary

In October 2013, Frederic Gillet proposed a polynomial-time algorithm for solving 3-SAT and 3-dimensional matching problems using conservative logic gates implemented on flow networks combined with minimum-cost flow methods.

**Author's Retraction (November 2013)**: The author added the following comment to the arXiv page: "The proposed method does not work. Updated the article with an analysis of why the general method suggested cannot work."

## Main Approach

### Core Idea

The paper proposes a reduction from NP-complete problems (3-SAT, 3-dimensional matching) to the minimum-cost flow problem, which can be solved in polynomial time. The approach consists of:

1. **Conservative Logic Gates on Flow Networks**: Implement Boolean logic gates (AND, OR, NOT, NAND, XOR, fan-out) as flow network subgraphs
2. **Flow Represents Boolean Values**: Unit flows (0 or 1) on edges represent Boolean variable assignments
3. **Negative Costs Drive Solutions**: Use edge costs of 0 or -1 to guide the minimum-cost flow algorithm toward satisfying assignments
4. **Polynomial-Time Solver**: Apply standard minimum-cost flow algorithms (e.g., minimum-mean cycle-canceling)

### Technical Construction

#### Logic Gates as Flow Networks

The paper shows how to construct flow network gadgets for:

- **AND/OR gates**: Using parallel paths with appropriate capacities and a central edge with negative cost (-1)
- **NOT gate**: Requires a constant "power" flow source and "ground" sink to generate output when input is 0
- **Fan-out gate**: Duplicates a flow signal (similar to NOT but different output routing)
- **NAND gate**: Composition of AND followed by NOT
- **XOR gate**: Built from NAND and fan-out gates

Each gate uses:
- **Capacity constraints** `u(e)` to limit flow values
- **Lower bound constraints** `l(e)` to force minimum flows
- **Negative costs** `c(e) = -1` on specific edges to make certain paths "cheaper"

#### Application to 3-Dimensional Matching

The paper attempts to solve 3-dimensional matching by:

1. Representing triplets as element nodes (E) and dimension nodes (X, Y, Z) as vertices
2. Adding source and sink vertices
3. Requiring flow of 2 through each selected triplet
4. Using a "diamond gate" to ensure exactly one flow of value 2 (not two flows of value 1) reaches each dimension node
5. Solving for minimum-cost flow with appropriate constraints

#### Application to 3-SAT

For 3-SAT with variables {x₁, x₂, ..., xₙ} and clauses:

1. Build a flow network with logic gates corresponding to each clause
2. Connect gates according to the CNF formula structure
3. Force the output to 1 using a lower bound constraint  `l(f) = 1`
4. Solve for minimum-cost flow
5. Read variable assignments from realized flows on variable edges

### The Critical Flaw

**The paper's core assumption is flawed**: It assumes that flow networks with negative costs can correctly model arbitrary logical circuits in a way that preserves the semantics of all gate combinations.

From the paper's own "Validity and Conclusion" section (page 26):

> "The proposed approach relies on the hypothesis that flow networks with costs can be used to model logical circuits (Turing Complete).
>
> **The work lacks a theoretical demonstration of this assumption.** One could try to show that arbitrary logic blocks can be put in series and parallel so that the various costs of the realized paths do not interfere with each other."

## The Error

### What Went Wrong

The fundamental error is that **the optimization objective (minimum cost) interferes with the logical constraints** in ways that cannot be controlled when gates are composed:

1. **Cost Interference**: When multiple logic gates are connected, the global cost minimization can select flows that satisfy local gate constraints but violate the intended logical relationships between gates

2. **Non-Compositionality**: While individual gates might work in isolation, their composition does not preserve logical semantics. The minimum-cost flow algorithm optimizes globally, not respecting the intended dataflow through the logical circuit

3. **Spurious Solutions**: The minimum-cost flow can find solutions that:
   - Satisfy all capacity and flow conservation constraints
   - Have negative total cost (appearing "valid")
   - But do NOT correspond to valid truth assignments for the original problem

4. **The "Diamond Gate" Issue**: The special gate designed to distinguish between one flow of value 2 versus two flows of value 1 (critical for 3-dimensional matching) likely does not work correctly when embedded in the full network with global cost optimization

### Why Minimum-Cost Flow Cannot Solve NP-Complete Problems

If this approach worked, it would imply P=NP, which contradicts:

- **50+ years of failed attempts** to find polynomial-time algorithms for NP-complete problems
- **Strong theoretical evidence** (though not proof) that P ≠ NP
- **Known barriers**: Such a reduction would need to overcome relativization, natural proofs, and algebrization barriers

The specific issue is that **local constraints (gate behavior) and global optimization (minimum cost) interact in unpredictable ways**. The minimum-cost flow algorithm has no mechanism to enforce that flows through the network represent consistent truth assignments that satisfy the logical formula.

### Author's Recognition

Frederic Gillet himself recognized the error and withdrew the paper in February 2014, explicitly stating "The proposed method does not work" and providing "an analysis of why the general method suggested cannot work."

## Key Lessons

1. **Gadget reductions are subtle**: Just because individual gadgets work in isolation doesn't mean their composition preserves desired properties

2. **Global vs. local optimization**: Using a global optimization objective (min-cost) to enforce local logical constraints is fragile and prone to interference

3. **Proof of correctness is essential**: The paper's own admission that it "lacks a theoretical demonstration" of its core assumption should have been a red flag

4. **Empirical testing reveals errors**: The author noted implementing the method would show "it simply works" - presumably implementation revealed the flaw

## Historical Context

- **Submission**: October 7, 2013 (v1)
- **Revisions**: Multiple versions (v1 through v6)
- **Withdrawal**: February 4, 2014 (v6, final)
- **Listed**: Entry #95 on Woeginger's P vs NP attempts list

This represents a responsible approach by the author: recognizing the error, analyzing why it doesn't work, and formally withdrawing the paper.

## References

1. Frederic Gillet. "Solving 3-SAT and 3-dimensional matching in polynomial time." arXiv:1310.1971 (withdrawn). https://arxiv.org/abs/1310.1971

2. Fredkin, Edward; Toffoli, Tommaso (1982). "Conservative logic". International Journal of Theoretical Physics 21 (3-4): 219-253.

3. Garey, Michael R.; Johnson, David S. "Computers and Intractability: A Guide to the Theory of NP-Completeness." W.H. Freeman, 1979.

4. Gerhard J. Woeginger. "The P-versus-NP page." https://www.win.tue.nl/~gwoegi/P-versus-NP.htm

## See Also

- [Original paper (PDF, v1)](https://arxiv.org/pdf/1310.1971v1)
- [Parent issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue #103](https://github.com/konard/p-vs-np/issues/103) - This formalization task
