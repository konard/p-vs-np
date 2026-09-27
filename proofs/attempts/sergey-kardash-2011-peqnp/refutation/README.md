# Sergey Kardash (2011) - Refutation

## Why the Proof Fails

Kardash's 2011 P=NP attempt contains a fundamental error: **the proof that a non-empty pair cleaning result implies satisfiability (Lemma 1) does not hold up for k ≥ 3**. Pair cleaning is a local consistency method. An empty result correctly proves that a formula is unsatisfiable, but the paper never justifies the step from local agreement between tables to one global satisfying assignment.

## The Fatal Error: Confusing Local with Global Consistency

### The Claim

Kardash claimed that his pair cleaning method — iterative pairwise removal of inconsistent variable assignments from overlapping clause groups — decides k-SAT in polynomial time O(n^12) for k=3.

## What Pair Cleaning Computes

The paper defines the operation in Definitions 3–15 ([`../original/ORIGINAL.md`](../original/ORIGINAL.md)):

1. **Clause groups** (Definition 3): clauses with the same set of variable indices form one group. A k-CNF with nt groups has *degree* nt (Definition 4).
2. **Tables** (Definitions 5–10): for every combination of k + 1 clause groups, the *value set* lists every assignment to the combination's variables that satisfies all of its clauses. When nt ≤ k + 1, Lemma 1's base case uses the single combination of all groups.
3. **Clearing** (Definitions 14–15): for two tables with common variables, a row of one table is deleted when no row of the other table agrees with it on those variables. Clearing all pairs is repeated until nothing changes.
4. **Result** (Definition 12): the result is *empty* when some table is empty. Theorem 1 claims that the formula is satisfiable exactly when the result is non-empty.

In constraint programming terms this is **pairwise consistency** (Bessière 2006) on the tables of clause combinations. It is not the same as arc consistency:

- **Arc consistency** removes *domain values of single variables* that have no support in some constraint. On the network with one binary constraint per 2-literal clause it removes nothing, because every clause over two variables allows both values of each of its variables.
- **Pair cleaning** removes *rows of joint tables* over up to (k + 1)·k variables, checking each row against every other table. This is strictly stronger: both 2-SAT formulas below fit in a single table, which is exactly the set of satisfying assignments, so pair cleaning empties it while arc consistency changes nothing.

Pair cleaning is:
- **Sound for UNSAT detection**: every row of a satisfying assignment's restriction survives every clearing, so if pair cleaning empties a table the formula is unsatisfiable
- **Not shown to be complete**: the paper's argument that a non-empty result contains a satisfying assignment (Lemma 1) has the gap described below

| Property | Pair cleaning | k-SAT (k ≥ 3) |
|----------|---------------|----------------|
| **Complexity** | Polynomial (O(n^12) for k = 3) | NP-complete |
| **What it checks** | Pairwise agreement of tables of k + 1 clause groups | One assignment satisfying all clauses |
| **Result when empty** | Formula is UNSAT ✓ | Correct |
| **Result when non-empty** | Satisfiability not proved for k ≥ 3 ✗ | **Unjustified claim** |

If pair cleaning did decide 3-SAT, it would be a polynomial-time algorithm for an NP-complete problem, so the burden is on Lemma 1. Its inductive step is where the proof fails.

## The Error in Lemma 1

### The Inductive Step

Kardash proves Lemma 1 by induction on nt (number of clause groups). The inductive step:

> Given Bnt(x) (formula without clause group Tnt+1) has a non-empty cleaned structure with a single-valued unclearable sub-structure V¹_B, extend this to Ant+1(x) by adding Tnt+1.

**The critical claim**: "these clause combinations [containing Tnt+1] don't give any new variables to clause combinations of RB and F(Tnt+1, Ti1, Ti2, …, Tik, A). This fact and the fact that in V¹_B all values of the same variables in different clause combinations are the same can give us a hint that value of each clause combination which contains Tnt+1 consisted of the same variable values as they presented in V¹_B."

**Why this fails**: The existence of a value V^B_{Tnt+1} in VC (the cleaned full structure) that matches V¹_B on common variables is assumed because "it can't be deleted during clearing." But clearing only guarantees that each surviving row agrees with *some* row of each other table, one table at a time. It does not guarantee that the particular single-valued choice V¹_B made for the smaller formula can be matched by one row of every table containing Tnt+1 simultaneously. The proof gives no argument for that step.

### Local Consistency Is Not Global Consistency

**Theorem** (well-known in constraint programming): There exist constraint satisfaction problem instances that are arc-consistent (no domain value can be eliminated by arc consistency) yet have no solution. The disequality triangle x ≠ y, y ≠ z, z ≠ x over Boolean domains (see below) is the smallest example.

Pair cleaning is stronger than arc consistency, so such instances do not refute it directly. The point is that local agreement, at any fixed level, needs an argument before it can imply a global solution. For k = 2 such an argument exists (next section). For k ≥ 3 the paper supplies none, and the formalization records this gap with informal axioms rather than a concrete counterexample.

## 2-SAT: Propagation Is Not a Decision Procedure

An earlier version of this refutation said that for k = 2 unit propagation and arc consistency coincide, that they decide 2-SAT, and that this is Krom's 1967 result; the Lean and Rocq files stated it as an assumption of type `True`. All three statements were wrong ([issue #587](https://github.com/konard/p-vs-np/issues/587)). The two formulas below are kept as counterexamples to that explanation and are checked in both proof assistants (section `TwoSATCounterexamples`).

**Counterexample 1**: (x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y).

- Every assignment falsifies one clause, so the formula is unsatisfiable.
- Unit propagation from the empty assignment does nothing: no clause is unit and none is falsified. A conflict appears only after a *decision* such as x := true.
- Arc consistency with one binary constraint per clause removes nothing.

**Counterexample 2**: the triangle x ≠ y, y ≠ z, z ≠ x over {true, false}.

- Two colours cannot colour an odd cycle, so it has no solution.
- It is arc-consistent with full domains: every value of every variable has a support on every edge.
- Its CNF encoding (x ∨ y) ∧ (¬x ∨ ¬y) ∧ (y ∨ z) ∧ (¬y ∨ ¬z) ∧ (z ∨ x) ∧ (¬z ∨ ¬x) is a fixpoint of unit propagation, and clause-wise arc consistency removes nothing. Merging the constraints on each scope does not help either (this merged form is what catches Counterexample 1).

**A complete method**: the implication graph has a node for each literal, and a clause l₁ ∨ l₂ gives the edges ¬l₁ → l₂ and ¬l₂ → l₁. A 2-CNF is unsatisfiable iff for some variable x the literals x and ¬x lie in the same strongly connected component, i.e. there are paths x ⇝ ¬x and ¬x ⇝ x (Aspvall, Plass & Tarjan 1979, linear time). For Counterexample 1 the paths are x → y → ¬x and ¬x → y → x; for the triangle it is x → ¬y → z → ¬x → y → ¬z → x. The proof assistants prove the soundness direction (`contradictory_cycle_unsat`) and exhibit both cycles.

| Procedure | Time | Decides 2-SAT? |
|-----------|------|----------------|
| Unit propagation, no decisions | Polynomial | **No** (Counterexample 1) |
| Arc consistency, one constraint per clause | Polynomial | **No** (Counterexample 1) |
| Arc consistency, constraints merged per scope | Polynomial | **No** (Counterexample 2) |
| Implication-graph strongly connected components (Aspvall, Plass & Tarjan 1979) | Linear | Yes |
| Resolution restricted to binary clauses (Krom 1967) | Polynomial | Yes |
| Unit propagation with decisions: try both values of a variable, keep one that propagates without conflict (Even, Itai & Shamir 1976) | Polynomial | Yes |
| Pair cleaning, k = 2 | Polynomial | Yes (informal sketch below, tested) |
| DPLL / CDCL with backtracking | Exponential worst case | Yes (and for every k) |

Pair cleaning for k = 2 does decide 2-SAT, but not for the reason the old text gave. Sketch (not formalized): at a non-empty fixpoint, pairwise consistency makes the projection of a table onto a set S of its variables the same for every table containing S, so each S has a well-defined projection P_S. If nt ≤ 3 there is a single table and it is exact. Otherwise every three variables occur in a common table (each lies in some clause group, and any three groups are part of some combination of three groups), so the binary network of the P_S for |S| = 2 is strongly 3-consistent. Every Boolean binary relation is closed under the majority operation, and for such networks strong 3-consistency implies global consistency (Jeavons, Cohen & Cooper 1998). A global solution of that network satisfies every clause, since P_S only contains rows that satisfy the clauses on S. The experiments in [`experiments/issue587`](../../../../experiments/issue587) compare pair cleaning with brute force on every 2-CNF over three variables and on random 2-CNFs over four to six variables.

This argument uses the majority closure of *binary* Boolean relations. Clauses with three literals are not closed under majority, so it does not carry over to k ≥ 3.

## The Subproblem Complexity Gap

### What Pair Cleaning Tracks
State per table: rows over the variables of k + 1 clause groups, at most (k + 1)·k variables
Number of states: O(nt^(k+1) · 2^((k+1)k)) — polynomial for fixed k

### What Satisfiability Requires
State per assignment: (value of x₁, value of x₂, …, value of x_m) — joint assignment to ALL variables
Number of states: 2^m — exponential

Pair cleaning never stores a joint assignment to all variables; Lemma 1 has to show that the local tables determine one, and that is the step it does not justify.

## The Correct Role of Local Consistency in SAT Solving

Local consistency (arc consistency, pairwise consistency, unit propagation) IS useful:
- **As preprocessing**: Reduce domain sizes before backtracking search
- **As propagation in CDCL solvers**: Within each search node, propagate locally
- **For 2-SAT specifically**: The implication-graph strongly connected component test decides satisfiability in linear time; propagation alone does not

But the paper gives no valid argument that it can replace backtracking search for k ≥ 3 SAT.

## Summary of Why the Claimed O(n^12) Algorithm Fails

1. **The algorithm runs in polynomial time** — this part is CORRECT
2. **An empty result correctly proves unsatisfiability** — pair cleaning is sound
3. **The algorithm is not shown to decide k-SAT** — pair cleaning is a local consistency (pairwise consistency on clause-combination tables)
4. **Lemma 1's inductive proof** has an unjustified step (local → global consistency)
5. **Therefore Theorem 1 is not established** and P=NP is not established

## References

- Aspvall, B., Plass, M. F., & Tarjan, R. E. (1979). "A linear-time algorithm for testing the truth of certain quantified Boolean formulas." *Information Processing Letters* 8(3), 121–123.
- Bessière, C. (2006). "Constraint propagation." In *Handbook of Constraint Programming*, ch. 3. Elsevier.
- Even, S., Itai, A., & Shamir, A. (1976). "On the complexity of timetable and multicommodity flow problems." *SIAM Journal on Computing* 5(4), 691–703.
- Jeavons, P., Cohen, D., & Cooper, M. C. (1998). "Constraints, consistency and closure." *Artificial Intelligence* 101(1–2), 251–265.
- Krom, M. R. (1967). "The decision problem for a class of first-order formulas in which all disjunctions are binary." *Zeitschrift für mathematische Logik und Grundlagen der Mathematik* 13, 15–20.
- Mackworth, A. K. (1977). "Consistency in networks of relations." *Artificial Intelligence* 8(1), 99–118.

## See Also

- [`../README.md`](../README.md) — Overview of the attempt
- [`../original/README.md`](../original/README.md) — Description of the original proof idea
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) — Markdown conversion of the original paper
- [`../proof/README.md`](../proof/README.md) — Forward proof formalization with the gap marked
- [`lean/KardashRefutation.lean`](lean/KardashRefutation.lean), [`rocq/KardashRefutation.v`](rocq/KardashRefutation.v) — Formal refutation, including the checked 2-SAT counterexamples
