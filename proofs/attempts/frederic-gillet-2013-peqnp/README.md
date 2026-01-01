# Frederic Gillet (2013) - P=NP Attempt

**Attempt ID**: 95 (from Woeginger's list)
**Author**: Frederic Gillet
**Year**: 2013
**Claim**: P=NP
**Paper**: "Solving 3-SAT and 3-dimensional matching in polynomial time"
**ArXiv**: [1310.1971](https://arxiv.org/abs/1310.1971) (withdrawn)
**Status**: Self-refuted by author in November 2013

## Summary

In October 2013, Frederic Gillet claimed to show that P=NP by demonstrating how the implementation of conservative logic gates on flow networks allows us to solve 3-SAT and 3-dimensional matching problems in polynomial time using standard minimum-cost flow methods.

**Important**: In November 2013, the author added an addendum stating: "The proposed method does not work. Updated the article with an analysis of why the general method suggested cannot work."

## Main Approach

### 1. Conservative Logic Gates

The approach builds on the work of Fredkin and Toffoli on conservative logic - computation models that reflect physical principles like:
- Reversibility of dynamical laws
- Conservation of additive quantities

### 2. Flow Network Implementation

Gillet proposes implementing logic gates (AND, OR, NOT, NAND, XOR, fan-out) as flow networks where:
- Boolean variables are represented as flows (0 or 1 unit)
- Logic gates are constructed using vertices, edges with capacities, and costs
- Key insight: Use negative costs (typically -1) on certain edges to guide minimum-cost flow algorithms toward correct logical behavior

### 3. The "Diamond Gate"

A critical innovation is a special gate that accepts flows of value 0, 1, or 2 and outputs:
- 2 if exactly one input is 2 and the other is 0
- 0 otherwise

This gate is used to ensure unique flow assignments in 3-dimensional matching.

### 4. Reduction Strategy

**For 3-Dimensional Matching**:
1. Transform the 3D matching problem into a flow network
2. Use diamond gates to enforce the constraint that each element receives exactly one flow of value 2 (not two flows of value 1)
3. Solve using polynomial-time minimum-cost flow algorithms
4. Extract the matching from the flow solution

**For 3-SAT**:
1. Transform Boolean clauses into flow networks using the logic gates
2. Set constraints: output must be 1 (satisfied formula)
3. Solve using minimum-cost flow
4. Extract variable assignment from the flow solution

## The Claimed Argument

1. **Turing Completeness**: Flow networks with costs can model arbitrary logical circuits
2. **Polynomial Reduction**: Any 3-SAT or 3D-matching instance can be transformed to a flow network in polynomial time (size differs by constant factor)
3. **Polynomial Solving**: Minimum-cost flow can be solved in polynomial time (e.g., minimum-mean cycle-canceling algorithm)
4. **Therefore**: P=NP

## The Error

### Author's Own Assessment

From page 26 of the paper:

> "The proposed approach relies on the hypothesis that flow networks with costs can be used to model logical circuits (Turing Complete).
>
> **The work lacks a theoretical demonstration of this assumption.** One could try to show that arbitrary logic blocks can be put in series and parallel so that the various costs of the realized paths do not interfere with each other."

### Critical Issues

#### 1. **Cost Interference Problem**

The fundamental flaw is that **minimum-cost flow optimization is global**, meaning costs from different parts of the circuit can interfere with each other in unexpected ways.

While the author claims that using only non-positive costs (0 or -1) prevents interference, this is **insufficient**:

- The minimum-cost flow algorithm optimizes over the **entire network simultaneously**
- There is no guarantee that the flow configuration minimizing global cost corresponds to correct logical evaluation
- Different logical paths may have different numbers of gates, leading to different total costs even for logically equivalent computations

#### 2. **Composability Not Proven**

The paper shows individual gates work in isolation but **does not prove** that:
- Gates can be arbitrarily composed while maintaining correctness
- Parallel compositions don't create unintended flow paths
- Series compositions preserve the cost structure needed for correctness

#### 3. **The Diamond Gate Flaw**

The diamond gate (pages 19-23) is supposed to distinguish between:
- One flow of value 2 (valid for 3D matching)
- Two flows of value 1 (invalid)

However, in a global minimum-cost optimization:
- The algorithm may find lower-cost solutions that violate the intended semantics
- The gate's behavior in isolation doesn't guarantee correct behavior when embedded in a larger network
- Flow can "leak" through unintended paths when multiple diamond gates interact

#### 4. **No Correctness Proof**

From the paper (page 26):

> "A practical approach consists in implementing the proposed method and show that it simply works (currently a work in progress)."

This reveals the core issue: **no formal proof of correctness was ever provided**. The author hoped empirical testing would validate the approach, which is methodologically backwards for a P vs NP claim.

## Why This Matters for Formalization

This attempt is particularly instructive because:

1. **Self-Aware Failure**: The author recognized and publicly acknowledged the flaw
2. **Subtle Error**: The mistake is not trivial - it involves the interaction between local correctness and global optimization
3. **Common Pattern**: Many P=NP attempts fail by assuming that local gadgets compose correctly without proving it

## Formalization Strategy

Our formal verification will focus on:

1. **Modeling flow networks** with capacities and costs
2. **Defining the logic gate constructions** (AND, OR, NOT, NAND, XOR, diamond gate)
3. **Attempting to prove composability** - this is where we expect to hit the error
4. **Formalizing the gap**: Showing that local correctness ≠ global correctness in minimum-cost flow networks

The formalization will help clarify exactly where and why the reduction fails.

## References

1. Gillet, F. (2013). "Solving 3-SAT and 3-dimensional matching in polynomial time" arXiv:1310.1971 (withdrawn)
2. Fredkin, E.; Toffoli, T. (1982). "Conservative logic", International Journal of Theoretical Physics 21 (3-4): 219–253
3. Woeginger, G. "The P-versus-NP page" https://www.win.tue.nl/~gwoegi/P-versus-NP.htm
4. Garey, M. R.; Johnson, D. S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness"

## See Also

- [Coq formalization](coq/)
- [Lean formalization](lean/)
- [Isabelle formalization](isabelle/)
