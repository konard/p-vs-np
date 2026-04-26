# Sergey Kardash (2011) - P=NP via Pair Cleaning Method for k-SAT

**Attempt ID**: 76 (from Woeginger's list)
**Author**: Sergey Kardash
**Year**: 2011 (arXiv submission July 30, 2011; revised May 31, 2012)
**Claim**: P = NP
**Status**: Refuted

## Summary

Sergey Kardash proposed a "pair cleaning" algorithm claimed to solve k-satisfiability (k-SAT) in polynomial time O(n^{3(k+1)}), specifically O(n^12) for 3-SAT. If correct, this would prove P=NP since 3-SAT is NP-complete.

## Directory Structure

- `README.md` - Overview of the attempt and error analysis
- `original/` - Original paper materials and English reconstruction
  - `README.md` - Description of the original proof idea
  - `ORIGINAL.md` - English reconstruction of the draft paper
  - `ORIGINAL.pdf` - Original arXiv draft
- `proof/` - Forward formalization of the claimed pair cleaning method
- `refutation/` - Formalization of why pair cleaning is incomplete for k-SAT

## Main Argument

### The Pair Cleaning Method

The approach introduces a hierarchical structure over k-CNF formulae:

1. **Clause Groups**: Given a k-CNF formula, group all clauses that involve the same set of k variable indices into a "clause group" T_{s₁s₂⋯sₖ}. The value set of a clause group is the set of all variable assignments to those k variables that satisfy every clause in the group.

2. **Clause Combinations**: A "clause combination" is any set of (k+1) clause groups. It captures overlapping constraints between groups sharing variables. The value set of a clause combination is the set of assignments to all involved variables that satisfy all clauses in all the groups.

3. **Relationship Structure**: The "relationship structure" R(A) is the set of ALL possible clause combinations of size (k+1) from the formula's clause groups. There are C(nt, k+1) such combinations, where nt is the number of clause groups.

4. **Pair Cleaning**: Iteratively "clean" pairs of clause combinations by removing any row from one combination's value table that has no matching assignment for the shared variables in the other combination's value table. Repeat until no more rows can be removed.

5. **Key Claim**: The result of pair cleaning is non-empty if and only if the k-CNF formula is satisfiable (Theorem 1, proved via Lemma 1 and Lemma 2).

### The Complexity Argument

The paper bounds:
- Values per clause group: < 2^k
- Values per clause combination: < 2^{k(k+1)}
- Clause combinations in R(A): C(nt, k+1)
- Comparisons per iteration: < 2^{2k(k+1)} · C(nt, k+1)²
- Iterations: < 2^{k(k+1)} · C(nt, k+1)
- Total operations: O(nt^{3(k+1)})

Then uses the bound 2^{-k}·n ≤ nt ≤ n to conclude the algorithm is O(n^{3(k+1)}), or O(n^12) for 3-SAT.

## The Error

### Fundamental Flaw: The Number of Clause Combinations is Exponential

**The Error**: The number of clause groups nt can itself be exponential in the number of variables m, and the number of clause combinations C(nt, k+1) is not polynomially bounded in the formula's input size n (number of clauses).

**Why This Matters**:

#### What the Paper Claims
The paper observes that nt ≤ n (the number of clause groups is at most the number of clauses), then concludes O(nt^{3(k+1)}) = O(n^{3(k+1)}).

#### The Hidden Problem: Constructing the Relationship Structure
The relationship structure R(A) contains C(nt, k+1) clause combinations. To run the algorithm, you must:
1. **Enumerate all C(nt, k+1) clause combinations** — this alone takes Θ(nt^{k+1}) time just to generate
2. **Compute the initial value sets** for each clause combination — each requires solving a small sub-SAT instance
3. **Run all pairwise comparisons** for each pair from C(nt, k+1) combinations

For k=3 (3-SAT), this means computing C(nt, 4) clause combinations, which is Θ(nt^4). Even if nt ≤ n, this gives O(n^4) combinations — but each combination's value table can have up to 2^{k(k+1)} = 2^{12} rows. Computing and comparing these tables is where the exponential constants hide.

#### The Critical Bound is Wrong
The paper bounds the number of clause combinations as C(nt, k+1) and treats this as O(nt^{k+1}), which it is. But the number of **iterations** of the outer loop is bounded by the maximum number of rows that can be deleted, which is:

    (total rows across all value tables) = C(nt, k+1) · 2^{k(k+1)}

For fixed k, the term 2^{k(k+1)} is a constant, so this is O(nt^{k+1}). However, the inner loop over all pairs at each iteration is O(C(nt, k+1)^2) = O(nt^{2(k+1)}). Together: O(nt^{3(k+1)}).

**The flaw**: The bound nt ≤ n is correct, but the proof of Lemma 1 — on which the correctness (Theorem 1) rests — contains an unjustified step.

### The Error in Lemma 1

**Lemma 1** claims: after pair cleaning, the result is non-empty ⟺ the formula is satisfiable.

The ⇐ direction (satisfiable ⇒ non-empty) is trivially correct.

The ⇒ direction (non-empty ⇒ satisfiable) is where the error lies. The inductive proof attempts to show that any non-empty result contains a "single-valued unclearable" structure which corresponds to a satisfying assignment.

**The critical gap**: In the inductive step, Kardash states that after extending from Bnt(x) (formula without clause group Tnt+1) to Ant+1(x), one can always extend the single-valued unclearable structure V¹_B to include Tnt+1. This relies on the assumption that "these clause combinations don't give any new variables to clause combinations of RB and F(Tnt+1, Ti1, Ti2, …, Tik, A)."

This assumption is **unjustified** in general. Clause group Tnt+1 may contain variables that appear in many other clause groups, and the constraints imposed by all these overlapping clause combinations may be mutually contradictory even when pairwise constraints are satisfied. This is precisely the phenomenon known as **constraint propagation incompleteness**: local consistency (pairwise arc consistency) does not imply global consistency.

### The Connection to Arc Consistency

The pair cleaning method is exactly **arc consistency** (AC-3 algorithm) applied to a constraint satisfaction problem. It is well-known in constraint programming that:

- **Arc consistency is polynomial to compute**: O(ed³) where e is number of constraints and d is domain size — matching Kardash's complexity bounds
- **Arc consistency does NOT imply satisfiability**: An arc-consistent CSP can still be unsatisfiable, and detecting this requires backtracking search

The classic counterexample: a 3-coloring problem on a graph that is arc-consistent but still requires exponential backtracking to determine satisfiability.

### Concrete Counterexample Type

Consider a 3-SAT formula that is arc-consistent (all pair-cleaning steps terminate without emptying any table) yet is unsatisfiable. Such formulas exist and are the reason why local consistency methods alone cannot solve NP-complete problems. Kardash's method would incorrectly report "satisfiable" on these instances.

### Why the Complexity Analysis Seems Correct

The complexity analysis (Section 3) of the algorithm's running time is **actually correct** — the algorithm does run in polynomial time. The error is not in the runtime bound but in the **correctness claim**: the algorithm does not correctly decide k-SAT. It computes arc consistency, which is a necessary but not sufficient condition for satisfiability.

## Why This Approach Is Tempting

The approach is appealing because:
- Pair cleaning terminates quickly (polynomial iterations)
- It correctly filters out many impossible assignments
- For easy instances (or 2-SAT, where arc consistency is complete), it works perfectly
- The lemma proofs appear rigorous at first glance

However, the gap between local pairwise consistency and global satisfiability is fundamental and cannot be closed without exponential backtracking in the worst case.

## Broader Context

### Arc Consistency and Constraint Satisfaction

In constraint programming:
- **Arc consistency (AC)**: For every pair of variables, remove domain values that have no consistent partner in the other variable's domain
- **AC is polynomial**: O(n·d³) where n = variables, d = domain size
- **AC ≠ satisfiability**: Arc-consistent instances can be unsatisfiable

Kardash's pair cleaning is equivalent to AC applied to the clause-combination constraint graph. The correctness claim (Theorem 1) would require that AC implies satisfiability for k-SAT, which is false for k ≥ 3.

### Why P ≠ NP Is Plausible

This attempt illustrates a common pattern: polynomial local consistency methods are confused with polynomial global satisfiability. The exponential hardness of SAT comes from the need to find a globally consistent assignment, which requires exponential search in the worst case despite any local simplifications.

## Formalization Goals

In this directory, we formalize:

1. **The Pair Cleaning Algorithm**: The iterative pairwise consistency procedure
2. **Arc Consistency**: What pair cleaning actually computes
3. **Correctness Claim**: What Kardash claimed (arc consistency implies satisfiability)
4. **The Gap**: Why arc consistency does not imply satisfiability for k ≥ 3
5. **The Counterexample Structure**: The type of instances where pair cleaning fails

## References

### Primary Sources

- **Original Claim**: Kardash, S. (2011). "Algorithmic complexity of pair cleaning method for k-satisfiability problem. (draft version)"
  - arXiv:1108.0408 [cs.CC]
  - Submitted: July 30, 2011; Revised: May 31, 2012
  - Available at: https://arxiv.org/abs/1108.0408
- **Reconstruction**: [`original/README.md`](original/README.md), [`original/ORIGINAL.md`](original/ORIGINAL.md), [`original/ORIGINAL.pdf`](original/ORIGINAL.pdf)

### Background on Arc Consistency and SAT

- **Woeginger's List**: Entry #76
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Arc Consistency**: Mackworth, A. K. (1977). "Consistency in networks of relations." Artificial Intelligence 8(1), 99–118.
- **AC-3 Algorithm**: Mackworth (1977); AC-3 runs in O(ed³) time.
- **Incompleteness of AC**: Well-known result in constraint programming — arc consistency is necessary but not sufficient for satisfiability of general CSPs.
- **2-SAT Completeness**: For 2-SAT, unit propagation (a form of arc consistency) IS complete (Krom 1967), which is why 2-SAT ∈ P.

## See Also

- [`original/README.md`](original/README.md) — Original proof idea and reconstruction
- [P = NP Framework](../../p_eq_np/) — General framework for evaluating P = NP claims
- [Repository README](../../../README.md) — Overview of the P vs NP problem
