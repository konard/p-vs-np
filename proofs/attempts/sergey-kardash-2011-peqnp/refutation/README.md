# Sergey Kardash (2011) - Refutation

## Why the Proof Fails

Kardash's 2011 P=NP attempt contains a fundamental error: **pair cleaning (arc consistency) does not decide satisfiability for k ≥ 3**.

## The Fatal Error: Confusing Local with Global Consistency

### The Claim

Kardash claimed that his pair cleaning method — iterative pairwise removal of inconsistent variable assignments from overlapping clause groups — decides k-SAT in polynomial time O(n^12) for k=3.

### The Problem

**Pair cleaning** is exactly **arc consistency** (specifically, a form of AC-3/AC-4) applied to a constraint satisfaction problem encoding of k-SAT. It is a fundamental theorem of constraint programming that:

| Property | Pair Cleaning (Arc Consistency) | k-SAT (k ≥ 3) |
|----------|--------------------------------|----------------|
| **Complexity** | Polynomial O(ed³) | NP-complete |
| **Correctness** | Local pairwise consistency only | Global satisfiability required |
| **Complete for** | 2-SAT (binary constraints) | k ≥ 3 requires backtracking |
| **Result when empty** | Formula is UNSAT ✓ | Correct |
| **Result when non-empty** | May still be UNSAT ✗ | **Incorrect claim** |

### Why This Is Fatal

Pair cleaning (arc consistency) is:
- **Sound for UNSAT detection**: If pair cleaning empties any table, the formula IS unsatisfiable
- **Incomplete for SAT detection**: If pair cleaning leaves all tables non-empty, the formula may still be UNSATISFIABLE

This incompleteness is the fundamental flaw in Theorem 1.

## The Error in Lemma 1

### The Inductive Step

Kardash proves Lemma 1 by induction on nt (number of clause groups). The inductive step:

> Given Bnt(x) (formula without clause group Tnt+1) has a non-empty cleaned structure with a single-valued unclearable sub-structure V¹_B, extend this to Ant+1(x) by adding Tnt+1.

**The critical claim**: "these clause combinations [containing Tnt+1] don't give any new variables to clause combinations of RB and F(Tnt+1, Ti1, Ti2, …, Tik, A). This fact and the fact that in V¹_B all values of the same variables in different clause combinations are the same can give us a hint that value of each clause combination which contains Tnt+1 consisted of the same variable values as they presented in V¹_B."

**Why this fails**: The existence of a value V^B_{Tnt+1} in VC (the cleaned full structure) that matches V¹_B on common variables is assumed because "it can't be deleted during clearing." But the clearing process is iterated until a fixpoint — a value can survive all pairwise clears yet still be part of an unsatisfiable sub-formula when considered globally. Pairwise consistency does not guarantee global consistency.

### The Constraint Propagation Incompleteness Theorem

**Theorem** (well-known in constraint programming): There exist constraint satisfaction problem instances that are arc-consistent (no domain value can be eliminated by pairwise consistency) yet have no solution.

**Corollary for k-SAT**: There exist k-SAT formulas (k ≥ 3) such that after applying pair cleaning to fixpoint, all value tables remain non-empty, yet the formula is unsatisfiable.

## A Concrete Counterexample Structure

### The Principle

Arc consistency (pair cleaning) considers only interactions between pairs of overlapping clause groups. Global consistency requires simultaneous compatibility across ALL clause groups, which involves checking exponentially many combinations.

### Specific Construction

Consider a 3-coloring problem instance (which reduces to 3-SAT):
- Graph vertices: variables (each taking 3 colors = values)
- Edges: constraints (adjacent vertices must have different colors)
- The formula is arc-consistent (every arc between adjacent vertices is consistent)
- But the graph is non-3-colorable (global constraint cannot be satisfied)

Pair cleaning on the SAT encoding of this instance would leave all tables non-empty (arc consistent) yet the formula is UNSAT. This disproves Kardash's Theorem 1.

### Example: Kempe's Fallacy Graph

A graph that is arc-consistent under 3-coloring constraints but cannot be 3-colored (e.g., certain Mycielski graphs or odd-cycle substructures) provides a concrete family of counterexamples where Kardash's algorithm would incorrectly output "satisfiable."

## The Subproblem Complexity Gap

### What Arc Consistency Tracks
State per arc: (value in domain of x_i, value in domain of x_j) for constraint (i,j)
Number of states: O(n · d²) — polynomial where d = domain size

### What Satisfiability Requires
State per assignment: (value of x₁, value of x₂, …, value of x_m) — joint assignment to ALL variables
Number of states: d^m — exponential

The gap grows exponentially with the number of variables. No polynomial procedure can enumerate all global states.

## The Correct Role of Arc Consistency in SAT Solving

Arc consistency (and pair cleaning) IS useful:
- **As preprocessing**: Reduce domain sizes before backtracking search
- **As propagation in CDCL solvers**: Within each search node, propagate locally
- **For 2-SAT specifically**: Unit propagation IS complete (Krom 1967)

But it cannot replace backtracking search for k ≥ 3 SAT.

## Summary of Why the Claimed O(n^12) Algorithm Fails

1. **The algorithm runs in polynomial time** — this part is CORRECT
2. **The algorithm does NOT correctly decide k-SAT** — this is the error
3. **The algorithm computes arc consistency**, which is necessary but not sufficient
4. **Lemma 1's inductive proof** has an unjustified step (local → global consistency)
5. **Therefore Theorem 1 is false** and P=NP is not established

## See Also

- [`../README.md`](../README.md) — Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) — Markdown conversion of the original paper
- [`../proof/README.md`](../proof/README.md) — Forward proof formalization with the gap marked
