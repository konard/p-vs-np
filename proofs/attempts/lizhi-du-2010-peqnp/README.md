# Lizhi Du (2010) - P=NP via Polynomial-Time 3SAT Algorithm

**Attempt ID**: 60 (from Woeginger's list)
**Author**: Lizhi Du
**Year**: 2010
**Claim**: P = NP
**Status**: Refuted

## Summary

In April 2010, Lizhi Du published a paper on arXiv claiming to solve the 3SAT problem in polynomial time, which would prove P = NP. The approach introduces several novel concepts including "checking trees, long unit paths, contradiction unit pairs, and 2-unit/3-unit layers" with the goal of transforming 3SAT instances into 2SAT instances that can be solved in polynomial time.

The paper has undergone extensive revisions (95 versions as of December 2025) but contains a fundamental algorithmic flaw that causes it to incorrectly classify satisfiable formulas as unsatisfiable.

## Main Argument

### The Approach

1. **Novel Concepts**: Du introduces checking trees, long unit paths, contradiction unit pairs, and unit layers as tools for analyzing 3SAT formulas
2. **3SAT to 2SAT Reduction**: The core idea is to reduce 3SAT problems to 2SAT problems, which are known to be solvable in polynomial time
3. **Algorithm 1**: A procedure that processes checking trees and determines satisfiability by analyzing unit layers and contradiction pairs
4. **Claimed Correctness**: If the algorithm works correctly, every 3SAT instance could be decided in polynomial time

### Key Technical Claim

The algorithm claims to correctly determine satisfiability by:
- Building checking trees that represent the logical structure of the formula
- Identifying contradiction pairs that would make the formula unsatisfiable
- Processing "useful units" through intersection operations to eliminate invalid assignments
- Concluding unsatisfiability when certain conditions are met

## The Error

### Fundamental Flaw: Incorrect Intersection Logic in Algorithm 1, Step 3

**The Error**: Algorithm 1, Step 3 contains a critical flaw in how it processes useful units.

**Specific Problem** (identified by He et al., 2024):
- **Location**: Step 3 of Algorithm 1, which processes destroyed checking trees
- **What Step 3 Does**: "For all (x,y) in distinct 3-unit layers that are not contradiction pairs of T, the useful units of x and y are set as the intersection between the useful units of x and y"
- **Why This Is Wrong**: This intersection operation incorrectly eliminates valid solution paths

### Counter-Example

The critique by He et al. (2024) presents an infinite family of satisfiable 3-CNF formulas that Du's algorithm incorrectly decides as unsatisfiable.

**Structure of Counter-Example**:
```
Initial clauses:
  (s ∨ t ∨ c̄)
  (s̄ ∨ t̄ ∨ r)
  ... intermediate clauses C₁, C₂, ..., Cₙ ...

New clause being tested:
  (a ∨ b ∨ c)
```

**What Happens**:
1. When checking whether (c, α) form a contradiction pair, Algorithm 1 removes c̄ and ᾱ from the checking tree
2. Step 3 is applied, forcing s and t to be eliminated from α's useful units through the intersection operation
3. The algorithm concludes that α has zero useful units in some layer
4. The algorithm incorrectly declares the formula unsatisfiable

**Why This Is a Counter-Example**:
- The formula is actually **satisfiable** (valid assignments exist)
- Du's algorithm incorrectly reports it as **unsatisfiable**
- The clauses C₁, C₂, ..., Cₙ can be composed of arbitrary literals satisfying the assumptions
- This creates an **infinite family** of formulas that the algorithm misclassifies

### Why The Error Occurs

The fundamental issue with Step 3's intersection operation:

1. **Incorrect Assumption**: The algorithm assumes that if two literals (x, y) don't form a contradiction pair, their useful units must intersect
2. **Why This Fails**: Useful units represent independent satisfying assignments for 2SAT subproblems, not mutually constrained sets
3. **Consequence**: Forcing intersection eliminates legitimate solution branches that remain valid in the overall formula
4. **Result**: Valid satisfying assignments are pruned from consideration, leading to false negatives

### Technical Analysis

**What Useful Units Represent**:
- Each useful unit corresponds to a potential partial assignment that satisfies certain 2-SAT subformulas
- Different useful units may represent independent satisfying paths through the solution space

**Why Intersection Fails**:
- Two literals that are not contradiction pairs may still have useful units that independently satisfy different parts of the formula
- Taking the intersection assumes these sets must overlap to form a valid solution
- This assumption breaks down because the overall 3SAT formula may allow either path to be valid
- By forcing intersection, the algorithm eliminates valid solution branches prematurely

**The Incorrect Logic**:
```
If (x, y) are not a contradiction pair:
  useful_units(x) ∩ useful_units(y)  [INCORRECT!]

This incorrectly assumes:
  Valid solutions must use assignments common to both x and y

But actually:
  Valid solutions might use assignments from x OR y (or neither)
```

## Broader Context

### Why This Approach Is Tempting

The approach is appealing because:
- **2SAT is in P**: 2SAT can be solved efficiently using graph-based algorithms
- **3SAT is NP-complete**: If we could reduce 3SAT to 2SAT in polynomial time, we'd prove P = NP
- **Structural Analysis**: Using checking trees and unit propagation is a legitimate SAT-solving technique

### The Critical Distinction: Sound Reduction vs. Heuristic Pruning

- **Sound Reduction**: A correct polynomial-time reduction from 3SAT to 2SAT that preserves satisfiability would prove P = NP
- **Heuristic Pruning**: Many SAT solvers use pruning techniques to eliminate search space, but they must be carefully designed to avoid eliminating valid solutions
- **The Gap**: Du's algorithm appears to be an aggressive pruning strategy that eliminates too much, causing false negatives

### Why This Error Is Subtle

The error is subtle because:
- The algorithm uses sophisticated concepts (checking trees, unit layers) that seem well-motivated
- The intersection operation in Step 3 might seem reasonable at first glance
- The error only manifests on specific formula structures
- The algorithm might work correctly on many simple test cases, making the bug hard to detect

## Revision History

The paper exhibits significant warning signs:
- **First Version**: April 12, 2010 (arXiv:1004.3702v1)
- **Latest Version**: v95 (December 22, 2025)
- **15 Years of Revisions**: Despite continuous updates, the fundamental flaw remains
- **No Peer-Reviewed Publication**: The paper has not been accepted in peer-reviewed venues
- **Community Rejection**: The complexity theory community does not accept this as a valid proof

This extensive revision history without mainstream acceptance indicates fundamental issues with the approach that the author has been unable to resolve.

## Formalization Goals

In this directory, we formalize:

1. **The Basic Setting**: What 3SAT is and why solving it in polynomial time would prove P = NP
2. **Du's Algorithm Structure**: The checking trees, useful units, and contradiction pairs (in simplified form)
3. **The Critical Step 3**: The flawed intersection operation
4. **Why This Would Imply P = NP**: If the algorithm were correct
5. **The Counter-Example**: A formal representation of formulas that the algorithm misclassifies
6. **The Refutation**: Proof that Step 3's logic is unsound

The formalization demonstrates that:
- The claim is well-formed and can be expressed formally
- The algorithm can be specified rigorously
- The critical flaw in Step 3 can be identified and proven incorrect
- Counter-examples exist that expose the algorithmic error

## References

### Primary Sources

- **Original Paper**: Du, L. (2010). "A Polynomial time Algorithm for 3SAT"
  - arXiv:1004.3702v1 (April 12, 2010)
  - Latest version: arXiv:1004.3702v95 (December 22, 2025)
  - Available at: https://arxiv.org/abs/1004.3702

- **Alternative Formulation**: Du, L. (2010). "A Polynomial Time Algorithm for Hamilton Cycle and Its Proof"
  - Presented at International Conference on Computer Design and Applications
  - Note: The Hamiltonian cycle approach appears to be related but separate from the main 3SAT paper

### Refutations

- **Formal Critique**: He, Y., et al. (2024). "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'"
  - arXiv:2404.04395 (April 2024)
  - Available at: https://arxiv.org/abs/2404.04395
  - Identifies the specific flaw in Algorithm 1, Step 3
  - Provides infinite family of counter-examples

### Context

- **Woeginger's List**: Entry #60
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Credits Dirk Gerrits for the reference

- **3SAT Problem**: Classic NP-complete problem
  - First problem proven NP-complete (Cook-Levin Theorem, 1971)
  - Central problem in computational complexity theory

## Key Lessons

1. **Algorithmic Correctness Requires Rigorous Proof**: Sophisticated algorithms with many moving parts need careful correctness proofs that consider all cases

2. **Counter-Examples Are Powerful**: A single counter-example (or family of counter-examples) can refute an algorithmic claim

3. **Pruning Must Be Sound**: In combinatorial search algorithms, pruning strategies must be proven sound—they must never eliminate valid solutions

4. **2SAT vs 3SAT Gap**: The jump from 2SAT (polynomial) to 3SAT (NP-complete) represents a fundamental complexity barrier that cannot be crossed with simple reduction techniques

5. **Empirical Testing Is Insufficient**: An algorithm might appear to work on many test cases but still contain subtle bugs that manifest only on specific inputs

6. **Persistence Without Progress**: Extensive revisions without peer acceptance suggests fundamental rather than fixable issues

7. **The Intersection Fallacy**: Just because sets represent related concepts doesn't mean taking their intersection preserves the properties you need

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [3SAT Problem](../../experiments/) - Background on 3-SAT and its complexity
- [Repository README](../../../README.md) - Overview of the P vs NP problem
