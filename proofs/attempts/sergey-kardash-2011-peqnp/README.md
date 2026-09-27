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

This assumption is **unjustified** in general. Clause group Tnt+1 may contain variables that appear in many other clause groups, and the constraints imposed by all these overlapping clause combinations may be mutually contradictory even when pairwise constraints are satisfied. This is precisely the phenomenon known as **constraint propagation incompleteness**: local consistency (here, pairwise agreement between clause-combination tables) does not by itself imply global consistency.

### What Pair Cleaning Computes

Pair cleaning (Definitions 3–15) builds one table for every combination of k + 1 clause groups, listing the assignments of the combination's variables that satisfy its clauses, and repeatedly deletes a row when some other table has no row agreeing with it on their common variables. In constraint programming terms this is **pairwise consistency** on the clause-combination tables. It is a local consistency method, but it is **stronger than arc consistency**: arc consistency only removes values of single variables, while pair cleaning removes rows of joint tables over up to (k + 1)·k variables. See [`refutation/README.md`](refutation/README.md#what-pair-cleaning-computes) for the full definition.

It is well-known in constraint programming that:

- **Local consistency is polynomial to compute** for tables of bounded size — matching Kardash's complexity bounds
- **Local consistency does NOT imply satisfiability in general**: an arc-consistent CSP can still be unsatisfiable (the Boolean triangle x ≠ y, y ≠ z, z ≠ x is one), and a stronger local consistency needs a proof before it can be trusted to decide a problem

For k = 2 such a proof exists (Boolean binary relations are closed under majority; Jeavons, Cohen & Cooper 1998), and pair cleaning does decide 2-SAT. For k ≥ 3 the paper's proof is Lemma 1, and its inductive step does not hold up.

### 2-SAT: Propagation Alone Is Not Enough

An earlier version of this analysis said that unit propagation and arc consistency decide 2-SAT and attributed that to Krom (1967). That is false ([issue #587](https://github.com/konard/p-vs-np/issues/587)); the formal refutation now keeps two checked counterexamples:

- **(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y)** is unsatisfiable, yet unit propagation from the empty assignment does nothing and arc consistency with one constraint per clause removes nothing.
- **The triangle x ≠ y, y ≠ z, z ≠ x** over Booleans is arc-consistent with full domains, yet has no solution; its CNF encoding is also a unit propagation fixpoint.

A complete polynomial method for 2-SAT is the implication-graph test: a 2-CNF is unsatisfiable iff some x and ¬x lie in the same strongly connected component (Aspvall, Plass & Tarjan 1979, linear time). Krom (1967) decides 2-SAT with resolution restricted to binary clauses, and Even, Itai & Shamir (1976) combine unit propagation with decisions.

### Why the Complexity Analysis Seems Correct

The complexity analysis (Section 3) of the algorithm's running time is **actually correct** — the algorithm does run in polynomial time. The error is not in the runtime bound but in the **correctness claim**: the paper does not prove that the algorithm decides k-SAT. It computes a local consistency, which is a necessary condition for satisfiability; Lemma 1's argument that it is also sufficient has a gap for k ≥ 3.

## Why This Approach Is Tempting

The approach is appealing because:
- Pair cleaning terminates quickly (polynomial iterations)
- It correctly filters out many impossible assignments
- For easy instances, and for 2-SAT (where its k + 1 = 3 group tables give strong 3-consistency), it works
- The lemma proofs appear rigorous at first glance

However, for k ≥ 3 the paper gives no valid argument that closes the gap between local pairwise consistency and global satisfiability.

## Broader Context

### Local Consistency and Constraint Satisfaction

In constraint programming:
- **Arc consistency (AC)**: For every constraint, remove domain values of one variable that have no consistent partner in the other variable's domain
- **Pairwise consistency**: For every two constraints (tables), remove tuples of one that have no tuple of the other agreeing on their common variables — this is what Kardash's pair cleaning computes on the clause-combination tables
- **Both are polynomial** for tables of bounded size
- **Local consistency ≠ satisfiability**: locally consistent instances can be unsatisfiable, unless the constraint language has a property (such as majority closure for Boolean binary relations) that turns local into global consistency

The correctness claim (Theorem 1) would require that pairwise consistency on (k + 1)-group tables implies satisfiability for k-SAT. The paper's proof of this (Lemma 1) is unjustified for k ≥ 3, and if it were true it would give a polynomial-time algorithm for 3-SAT.

### Why P ≠ NP Is Plausible

This attempt illustrates a common pattern: polynomial local consistency methods are confused with polynomial global satisfiability. The exponential hardness of SAT comes from the need to find a globally consistent assignment, which requires exponential search in the worst case despite any local simplifications.

## Formalization Goals

In this directory, we formalize:

1. **The Pair Cleaning Algorithm**: The iterative pairwise consistency procedure
2. **Local Consistency**: What pair cleaning actually computes (pairwise consistency on clause-combination tables)
3. **Correctness Claim**: What Kardash claimed (a non-empty cleaned structure implies satisfiability)
4. **The Gap**: The unjustified inductive step of Lemma 1 for k ≥ 3
5. **2-SAT Counterexamples**: Checked formulas showing that unit propagation and arc consistency do not decide 2-SAT, and the implication-graph cycles that refute them

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
- **Pairwise consistency**: Bessière, C. (2006). "Constraint propagation." In *Handbook of Constraint Programming*, ch. 3. Elsevier.
- **Local to global consistency**: Jeavons, P., Cohen, D., & Cooper, M. C. (1998). "Constraints, consistency and closure." Artificial Intelligence 101(1–2), 251–265.
- **2-SAT ∈ P**: Krom, M. R. (1967). "The decision problem for a class of first-order formulas in which all disjunctions are binary." Zeitschrift für mathematische Logik und Grundlagen der Mathematik 13, 15–20 (binary resolution); Even, S., Itai, A., & Shamir, A. (1976). "On the complexity of timetable and multicommodity flow problems." SIAM Journal on Computing 5(4), 691–703; Aspvall, B., Plass, M. F., & Tarjan, R. E. (1979). "A linear-time algorithm for testing the truth of certain quantified Boolean formulas." Information Processing Letters 8(3), 121–123 (implication-graph strongly connected components). Unit propagation and arc consistency alone do not decide 2-SAT.

## See Also

- [`original/README.md`](original/README.md) — Original proof idea and reconstruction
- [P = NP Framework](../../p_eq_np/) — General framework for evaluating P = NP claims
- [Repository README](../../../README.md) — Overview of the P vs NP problem
