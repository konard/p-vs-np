# Charles Sauerbier (2002) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Proof Attempts](../../README.md)

---

## Metadata

- **Author**: Charles Sauerbier
- **Year**: 2002
- **Claim**: P = NP
- **Paper**: "Three complete deterministic polynomial algorithms for 3SAT"
- **arXiv ID**: [cs/0205064](https://arxiv.org/abs/cs/0205064)
- **Status**: **Refuted** (Error found in September 2003)

## Overview

In May 2002, Charles Sauerbier presented three algorithms claiming to solve the 3SAT problem (and by extension, the general SAT problem) in deterministic polynomial time. If correct, this would prove P = NP, as SAT is NP-complete.

The algorithms were based on constraint propagation over specialized structures representing all possible assignments to subsets of variables. However, a critical error was discovered in September 2003.

## Main Approach

### Core Concept

Sauerbier's approach differs from conventional SAT solvers by operating on specialized structures:

1. **C/DNF Structure (A)**: Represents the complete set of all possible assignments to subsets of variables
   - Equivalent to a conjunction of disjunctive normal form (DNF) expressions
   - Each element contains assignments to 3-variable subsets

2. **C/CNF Structure (D)**: Represents the set of all possible constraints on subsets of variables
   - Equivalent to a conjunction of conjunctive normal form (CNF) expressions
   - Dual representation to C/DNF

### The Three Algorithms

#### Algorithm 1: Assignment Reduction in A
- **Process**: Start with all possible assignments, iteratively remove assignments inconsistent with SAT clauses
- **Key Operation**: Constraint propagation via "reduce" operator
- **Claimed Runtime**: O(|V|^12) worst case
- **Output**: Certificate of satisfiability or non-satisfiability

#### Algorithm 2: Constraint Propagation in D
- **Process**: Start with no constraints, iteratively add constraints from SAT clauses and propagate derived constraints
- **Key Difference**: Corrected version of algorithm in earlier paper [5]
- **Claimed Runtime**: O(|V|^6) worst case
- **Output**: Certificate of satisfiability or non-satisfiability

#### Algorithm 3: Iteration on P
- **Process**: Iterate over all 3-variable subsets, checking assignment consistency
- **Claimed Runtime**: O(|V|^9) worst case
- **Output**: Certificate of satisfiability or non-satisfiability

### Mathematical Framework

The paper defines:
- **V**: Set of Boolean variables
- **C**: Set of 3-CNF clauses
- **P**: Set of all 3-variable subsets of V (size |V|^3)
- **D**: Structure mapping each element of P to constraints
- **A**: Structure mapping each element of P to admissible assignments

Key claim: The CNF expression acts as a "basis set" of constraints from which all constraints can be derived via propagation.

## The Error

### Discovery
In September 2003, a hole was found in the algorithm's reasoning.

### Nature of the Error

According to Woeginger's P vs NP page:
> "An eleventh hour change admits a path inconsistency"

More specifically, from the source:
> "An improper closure of a path to a cycle against a root not supportive of the path"

### Technical Explanation (from the 2019 revision)

The critical flaw is explained in Section 4 ("Discussion") of the paper:

**The Central Problem**: The algorithm in the original version [5] failed because:

1. **Missing A Priori Knowledge**: The algorithm assumed that constraint propagation could work on structure D containing only the clausal constraints from the CNF expression

2. **False Support**: Certain 3SAT instances can produce what Sauerbier calls "false support" - a set of assignments that appears consistent when checking only elements of D/A corresponding to clauses in the expression, but is actually unsatisfiable

3. **Incomplete Propagation**: Restricting constraint propagation to only those elements of D where clauses are defined fails to detect inconsistencies that only become apparent when considering ALL 3-variable subsets

### The Corrected Algorithms

The 2019 revision presents corrected algorithms that:
- Operate on ALL elements of P (all 3-variable subsets), not just those with clauses
- This changes the approach but also increases complexity
- **Critical Issue**: Even with corrections, the polynomial time claim relies on the correctness of the constraint propagation terminating with the right answer

### Example of Failure Case

Appendix A provides a concrete example with V = {v0, v1, v2, v3, v4} and 24 clauses that:
- Produces "false support" in a restricted subset
- Appears satisfiable when checking only clause-relevant subsets
- Is actually unsatisfiable when all 3-variable subsets are considered

The admitted assignments that fool the restricted algorithm:
```
{(-v0, v1, v4), (v0, -v1, v4), (v0, v2, -v3), (-v0, -v2, -v3),
 (-v1, -v2, -v3), (v1, v2, -v3), (-v2, -v3, -v4), (v2, v3, -v4)}
```

This creates a "chain of resolution" that forms an invalid cycle, which the restricted algorithm fails to detect.

## Why This Doesn't Prove P=NP

### Fundamental Issues

1. **Exponential Structure Size**: The structures A and D have size O(|V|^3) in number of elements, but each element can represent up to 8 assignments/constraints. For general SAT (not just 3SAT), this grows exponentially.

2. **Hidden Complexity**: The "reduce" operator has worst-case O(|V|^9) runtime, making the overall algorithm O(|V|^12). However, the correctness argument assumes that constraint propagation always terminates correctly, which is not proven.

3. **Incorrect Complexity Analysis**: The claimed polynomial bounds count operations on the structures, but:
   - The structures themselves may require exponential initialization for general SAT
   - The propagation process may require exponential iterations in pathological cases
   - The paper only analyzes 3SAT, not general SAT

4. **The "A Priori Knowledge" Requirement**: Section 5.2 explicitly states:
   > "It is important to note that absent A containing an a priori known set of Boolean sequences (binary strings) and consistent constraints on the variables the algorithm described here is not assured to reliably produce a correct result."

   This admission undermines the claim that the algorithm solves SAT in polynomial time from scratch.

## Formalization Goals

This directory contains formal verification attempts in three proof assistants to:

1. **Formalize the core structures** (C/DNF, C/CNF, structures A and D)
2. **Formalize the three algorithms** as presented in the paper
3. **Formalize the example from Appendix A** that demonstrates the false support problem
4. **Identify the gap** in the polynomial-time claim through formal proof
5. **Document why** the corrected algorithms still don't prove P=NP

## Directory Structure

```
charles-sauerbier-2002-peqnp/
├── README.md (this file)
├── coq/
│   ├── Structures.v           # C/DNF and C/CNF structures
│   ├── Algorithms.v            # The three algorithms
│   ├── Example.v               # Appendix A counterexample
│   └── Error.v                 # Formalization of the error
├── lean/
│   ├── Structures.lean         # C/DNF and C/CNF structures
│   ├── Algorithms.lean         # The three algorithms
│   ├── Example.lean            # Appendix A counterexample
│   └── Error.lean              # Formalization of the error
└── isabelle/
    ├── Structures.thy          # C/DNF and C/CNF structures
    ├── Algorithms.thy          # The three algorithms
    ├── Example.thy             # Appendix A counterexample
    └── Error.thy               # Formalization of the error
```

## Key Insights for Formal Verification

1. **Termination**: Proving that constraint propagation terminates is straightforward (monotonic decrease in assignments), but proving it terminates with the correct answer is not.

2. **Completeness Gap**: The algorithm claims to be "complete" by producing certificates, but the certificates are only valid if the propagation process is correct for ALL instances.

3. **The False Support Problem**: This is the key to formalizing the error - showing that there exist SAT instances where the restricted algorithm gives wrong answers.

4. **Complexity vs Correctness**: Even if the algorithm is correct after the fix, the polynomial-time claim requires careful analysis of:
   - Structure initialization cost
   - Propagation iteration count
   - Reduce operator complexity

## References

1. **Original Paper**: Sauerbier, C. (2002). "Three complete deterministic polynomial algorithms for 3SAT." arXiv:cs/0205064v3
2. **Woeginger's List**: Entry #6 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. **Parent Issue**: #72 - Formalize Charles Sauerbier (2002) - P=NP
4. **Related Work**: Cook, S. (1971). "The complexity of theorem-proving procedures." (Established NP-completeness of SAT)

## Status

- ✅ README documentation complete
- 🚧 Coq formalization: In progress
- 🚧 Lean formalization: In progress
- 🚧 Isabelle formalization: In progress
- ⏳ Error identification: Pending formalization completion

---

**Note**: This is a formalization of a **refuted** attempt. The goal is educational - to understand why the approach fails and to practice formal verification of algorithmic claims.

**Last Updated**: 2025-10-26
