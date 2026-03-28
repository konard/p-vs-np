# Sergey Gubin (2006) - P=NP via Polynomial-Time TSP Algorithm

**Attempt ID**: 33 (from Woeginger's list)
**Author**: Sergey Gubin
**Year**: 2006 (October, revised through 2008)
**Claim**: P = NP
**Status**: Refuted

## Summary

In October 2006, Sergey Gubin proposed a polynomial-time algorithm for the Traveling Salesman Problem (TSP), claiming this would establish P = NP. The approach centered on formulating the Asymmetric Traveling Salesman Problem (ATSP) polytope using a polynomial-sized linear program. Gubin also developed related work on polynomial-time SAT solving, attempting to reduce SAT to 2-SAT in polynomial time.

Both approaches were comprehensively refuted by the research community, with critical errors identified by Radosław Hofman (2006) for the TSP work and by Ian Christopher, Dennis Huo, and Bryan Jacobs (2008) for the SAT solving algorithm.

## Main Argument

### The TSP/Linear Programming Approach

1. **Linear Program Formulation**: Gubin proposed expressing the ATSP polytope using an asymmetric polynomial-sized linear program
2. **Polynomial-Time Solvability**: Since linear programming problems can be solved in polynomial time (via ellipsoid method or interior point methods), this would imply TSP can be solved in polynomial time
3. **Implication**: Since TSP is NP-complete (via reduction from Hamiltonian Cycle), this would prove P = NP

### The SAT Solving Approach

In related work, Gubin also claimed:

1. **SAT to 2-SAT Reduction**: A polynomial-time reduction from general SAT to 2-SAT
2. **2-SAT Solvability**: 2-SAT is known to be solvable in polynomial time
3. **Implication**: Since 3-SAT is NP-complete, a correct polynomial-time reduction to 2-SAT would prove P = NP

## The Errors

### Error 1: Flawed TSP Linear Programming Formulation

**The Critical Flaw**: The ATSP polytope formulation does not correctly capture all and only valid TSP tours.

**Details of the Error** (identified by Hofman, 2006):

1. **Non-Integer Solutions**: The linear program formulation can have extreme points that are not integral, meaning they don't correspond to valid tours
   - The approach uses equations based on column and row constraints
   - While such equations might work for some integer-restricted solutions, for non-integer values there can be an infinite number of assignments for variable values
   - This means the LP may produce fractional solutions that don't represent actual tours

2. **Missing Correspondence**: There is no proven one-to-one correspondence between:
   - The extreme points of the LP polytope
   - Valid TSP tours

3. **Size-Dependent Failure**: Hofman demonstrated that "it is only a matter of size when such an approach can be proven incorrect" - meaning counter-examples exist where the formulation fails

4. **Fundamental Issue**: Creating a compact LP formulation of an NP-complete problem that maintains integral extreme points corresponding to all solutions would indeed prove P = NP - but this is precisely what we believe is impossible

**Why This Pattern Recurs**: This error is similar to other failed attempts (notably Moustapha Diaby's 2004 work, also on Woeginger's list as entry #14) that try to use linear programming to solve NP-complete problems. The critical distinction between:
- **Integer Linear Programming (ILP)**: Requires integer solutions - NP-complete
- **Linear Programming (LP)**: Allows fractional solutions - polynomial time

Converting an ILP to an LP while maintaining integrality is the hard part, and claiming this without rigorous proof is where these attempts fail.

### Error 2: Flawed SAT to 2-SAT Reduction

**The Critical Flaw** (identified by Christopher, Huo, and Jacobs, 2008): The reduction from SAT to 2-SAT contains multiple logical errors.

**Specific Errors**:

1. **Exponential Blowup Not Accounted For**: The reduction "fails to account for the exponential blowup in clauses" that occurs during the transformation from k-SAT to 2-SAT
   - While standard techniques can convert k-SAT to 3-SAT with polynomial blowup, converting to 2-SAT while preserving satisfiability equivalence typically requires exponential overhead
   - Gubin's claim of polynomial-time reduction overlooks this fundamental barrier

2. **Flawed Clause Simplification**: The method of "simplifying boolean expressions overlooks cases where variable assignments" create contradictions
   - The algorithm doesn't properly handle all cases where the reduction produces inconsistent constraints
   - This means the reduction may incorrectly report unsatisfiable instances as satisfiable, or vice versa

3. **Missing Complexity Analysis**: Gubin "does not adequately address why his iterative refinement process terminates in polynomial time"
   - The algorithm may contain hidden exponential behavior in its recursive structure
   - Without rigorous proof that the process terminates in polynomial time, the claim of polynomial-time reduction is unsubstantiated

4. **Conflating Heuristics with Proofs**: The work "conflates practical heuristic improvements with genuine polynomial-time solutions to an NP-complete problem"
   - Showing that an algorithm works well on some instances is not the same as proving it works correctly in polynomial time on all instances

### Error 3: Lack of Rigorous Proof

**The Overarching Issue**: Both approaches lack the rigorous mathematical proofs required to establish their claims:

1. **No Proof of Correctness**: The algorithms' correctness is asserted rather than proven
2. **No Proof of Polynomial Running Time**: The polynomial-time complexity is claimed without detailed analysis showing all cases terminate in polynomial time
3. **No Counter-Example Analysis**: The work doesn't address why previous attempts at similar reductions have failed
4. **Ignoring Known Barriers**: The proofs don't explain how they overcome known barriers in complexity theory

## Why These Approaches Cannot Work

### The LP/TSP Barrier

For a polynomial-sized LP formulation of TSP to solve the problem:
- Every extreme point of the LP polytope must correspond to exactly one valid TSP tour
- Every valid TSP tour must correspond to exactly one extreme point
- The LP optimal solution must be an extreme point

Establishing this correspondence rigorously is equivalent to solving P vs NP itself. Simply asserting it without proof is insufficient.

### The SAT to 2-SAT Barrier

If SAT could be reduced to 2-SAT in polynomial time while preserving satisfiability:
- This would indeed prove P = NP (since 3-SAT is NP-complete and 2-SAT is in P)
- However, all known reductions that preserve satisfiability require exponential blowup
- This is not an accident - it reflects the fundamental complexity difference between 2-SAT and 3-SAT

The existence of a polynomial-time truth-preserving reduction would be a major breakthrough, not a straightforward technical result.

## Historical Context and Community Response

### Timeline

- **October 2006**: Gubin submits TSP paper to arXiv (cs/0610042)
- **October 2006**: Hofman publishes critique of the TSP approach (cs/0610125)
- **November 2006**: Gubin revises the TSP paper
- **April 2008**: Christopher, Huo, and Jacobs publish comprehensive refutation of the SAT solving approach (arXiv:0804.2699)
- **September 2008**: Gubin publishes final revision of TSP paper

### Community Reception

- The computational complexity community did not accept these proofs
- Multiple refutations were published
- The work has not been cited as a valid contribution to resolving P vs NP
- Listed on Woeginger's compilation of failed P vs NP proof attempts

## Formalization Goals

In this directory, we formalize:

1. **The TSP Claim**: What it would mean to have a polynomial-sized LP formulation that correctly solves TSP
2. **The SAT Reduction Claim**: What a polynomial-time SAT to 2-SAT reduction would require
3. **The Critical Properties**: The one-to-one correspondence needed for the LP approach, and the satisfiability-preserving property needed for the SAT reduction
4. **Why These Would Imply P = NP**: Formal verification of the implication chains
5. **The Gaps**: Where the proofs fail - existence of the required properties is asserted, not proven
6. **Counter-Example Structure**: Formalization of why counter-examples can exist (following Hofman's analysis)

The formalization demonstrates that:
- The claims are well-formed and can be expressed formally
- The critical steps (proving correspondence for LP, proving polynomial blowup for SAT reduction) are non-trivial
- Without rigorous proofs of these properties, the arguments fail
- The approaches face fundamental barriers that make them unlikely to succeed

## Classification of Errors

### Error Type
- **Primary**: Unsubstantiated claims - asserting critical properties without proof
- **Secondary**: Missing complexity analysis - not rigorously proving polynomial-time bounds
- **Tertiary**: Conflating special cases with general solutions

### Severity
- **Fatal**: The missing proofs are the entire substance of resolving P vs NP
- **Not fixable**: The properties claimed are precisely what makes P vs NP hard

### Common Pattern
This represents a recurring pattern in failed P vs NP attempts:
1. Identify a known polynomial-time technique (LP solving, 2-SAT solving)
2. Claim an NP-complete problem can be reduced to this technique
3. Assert the reduction works without rigorous proof
4. Overlook the fundamental complexity barriers that make such reductions unlikely to exist

## What Would Be Required for Validity

### For the TSP/LP Approach

1. **Rigorous polytope characterization**: Prove that the LP polytope has a specific structure
2. **Integrality proof**: Show that all extreme points are integral and correspond to tours
3. **Completeness proof**: Show that all valid tours are represented as extreme points
4. **Uniqueness proof**: Show the correspondence is one-to-one
5. **Address counter-examples**: Resolve Hofman's critique with formal proofs, not just rebuttals

### For the SAT Reduction Approach

1. **Correctness proof**: Prove the reduction preserves satisfiability in both directions
2. **Polynomial blowup proof**: Rigorously prove the number of clauses grows only polynomially
3. **Termination analysis**: Prove all iterative procedures terminate in polynomial time
4. **Handle all cases**: Address the contradictory cases identified by Christopher et al.
5. **Explain the breakthrough**: If such a reduction exists, explain why previous attempts failed

## Educational Value

This attempt teaches several important lessons:

1. **The LP vs ILP Distinction**: Understanding why efficient LP solving doesn't immediately solve NP-complete integer programming problems
2. **Reduction Complexity**: Not all reductions preserve complexity - reducing a hard problem to an easy problem in polynomial time would be extraordinary
3. **Proof Rigor**: In complexity theory, claims must be backed by rigorous proofs covering all cases
4. **The Barrier of Lower Bounds**: Proving that something cannot be done efficiently is fundamentally difficult
5. **Counter-Example Power**: A single valid counter-example can refute a universal claim
6. **Community Review**: The importance of peer review in catching subtle errors

## References

### Primary Sources

- **Original TSP Paper**: Gubin, S. (2006). "A Polynomial Time Algorithm for The Traveling Salesman Problem"
  - arXiv:cs/0610042 (multiple versions, final revision September 2008)
  - https://arxiv.org/abs/cs/0610042

### Refutations

- **Hofman's TSP Critique (2006)**: Hofman, R. (2006). "Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem"
  - arXiv:cs/0610125
  - https://arxiv.org/abs/cs/0610125

- **SAT Solver Refutation (2008)**: Christopher, I., Huo, D., & Jacobs, B. (2008). "A Critique of a Polynomial-time SAT Solver Devised by Sergey Gubin"
  - arXiv:0804.2699
  - https://arxiv.org/abs/0804.2699

### Context

- **Woeginger's List**: Entry #33
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Related Failed Attempt**: Moustapha Diaby (2004) - Entry #14 on Woeginger's list
  - Similar LP-based approach to TSP with similar errors
  - See: [../moustapha-diaby-2004-peqnp/](../moustapha-diaby-2004-peqnp/)

## Key Lessons

1. **Extraordinary Claims Require Extraordinary Proofs**: Claiming to solve P vs NP requires rigorous, detailed proofs at every step
2. **Know the Barriers**: Understanding why previous attempts failed is crucial
3. **LP ≠ ILP**: The gap between linear programming and integer linear programming is fundamental to complexity theory
4. **Reductions Have Costs**: Not all problem transformations preserve complexity
5. **Assertions ≠ Proofs**: Stating that a property holds is not the same as proving it
6. **Counter-Examples Are Decisive**: Valid counter-examples definitively refute universal claims

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Moustapha Diaby Attempt (2004)](../moustapha-diaby-2004-peqnp/) - Similar LP-based TSP approach
- [Repository README](../../../README.md) - Overview of the P vs NP problem
- [Basic Formalizations](../../basic/) - Fundamental definitions used in these formalizations
