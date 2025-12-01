# Moustapha Diaby (2004) - P=NP via Linear Programming Formulation of TSP

**Attempt ID**: 14 (from Woeginger's list)
**Author**: Moustapha Diaby
**Year**: 2004
**Claim**: P = NP
**Status**: Refuted

## Summary

In October 2004, Moustapha Diaby proposed a polynomial-sized linear programming (LP) formulation for the Travelling Salesman Problem (TSP), claiming this would imply P = NP. The argument was that if TSP (an NP-complete problem) can be formulated as a polynomial-sized LP problem, and since LP problems can be solved in polynomial time, this would prove P = NP.

## Main Argument

### The Approach

1. **Network Flow-Based Model**: Diaby constructed a network flow-based linear programming formulation of the TSP
2. **Polynomial Size**: The formulation has O(n^9) variables and O(n^7) constraints, which is polynomial in the problem size
3. **LP Solvability**: Linear programming problems can be solved in polynomial time (e.g., using the ellipsoid method or interior point methods)
4. **Claimed Implication**: If TSP can be formulated as a polynomial-sized LP and solved efficiently, then P = NP

### Key Technical Claim

The crucial claim was that there exists a **one-to-one correspondence** between:
- The extreme points of the LP polytope
- Valid TSP tours

If this correspondence held, then solving the LP problem would directly give the optimal TSP solution.

## The Error

### Fundamental Flaw: Missing One-to-One Correspondence

**The Error**: The claimed one-to-one correspondence between LP extreme points and TSP tours does not hold.

**Why This Matters**:
- For the approach to work, every extreme point of the LP polytope must correspond to exactly one valid TSP tour, and vice versa
- If this correspondence fails, then solving the LP may give solutions that are NOT valid TSP tours
- Or, the LP may have multiple extreme points corresponding to the same tour
- Either way, solving the LP doesn't necessarily solve the TSP

### Counter-Example (Hofman, 2006 & 2025)

Radosław Hofman provided counter-examples demonstrating that:

1. **Non-Integral Extreme Points**: The LP formulation can have extreme points that are not integral, meaning they don't correspond to valid tours
2. **Missing Tours**: Some valid TSP tours may not correspond to extreme points of the LP polytope
3. **Specific Counter-Example** (2025): A graph with 366 nodes in two main clusters, where each node has exactly four connections, demonstrates that the LP model does not maintain the required correspondence

### Why The Correspondence Fails

The fundamental issue is that:
- The TSP has an exponential number of tours (roughly (n-1)!/2 for complete graphs)
- The LP polytope may have a different structure
- There is no proof that Diaby's polynomial-sized LP formulation correctly captures ALL and ONLY the valid TSP tours as its extreme points

This is actually expected: if it were possible to create a compact LP formulation of an NP-complete problem that maintains integral extreme points corresponding to all solutions, this would indeed prove P = NP - but this is precisely what we believe is impossible!

## Broader Context

### Why This Approach Is Tempting

The approach is appealing because:
- LP problems ARE solvable in polynomial time
- Many important problems DO have efficient LP formulations
- The TSP can be formulated as an Integer Linear Program (ILP)

### The Critical Distinction: LP vs ILP

- **Integer Linear Programming (ILP)**: Requires solutions to be integers - this IS hard (NP-complete)
- **Linear Programming (LP)**: Allows fractional solutions - this IS efficient (polynomial time)
- **The Gap**: Converting an ILP to an LP while maintaining integrality of solutions is the hard part

Diaby's error was in claiming that his LP formulation maintains integral extreme points corresponding to TSP tours without providing adequate proof of this critical property.

## Ongoing Controversy

The claim has been:
- **Refuted**: By Hofman (2006, 2025) with specific counter-examples
- **Defended**: Diaby published rebuttals claiming the counter-examples violate constraints
- **Generally Rejected**: The complexity theory community does not accept this as a valid proof of P = NP

The fact that this argument has been revised multiple times (the paper has been updated several times since 2004) and counter-examples continue to be published (as recently as 2025) indicates fundamental issues with the approach.

## Formalization Goals

In this directory, we formalize:

1. **The Basic Claim**: What it would mean to have a polynomial-sized LP formulation of TSP
2. **The Critical Property**: The required one-to-one correspondence between extreme points and tours
3. **Why This Would Imply P = NP**: If the correspondence held
4. **The Gap**: Where the proof fails (existence of the correspondence is not proven)

The formalization demonstrates that:
- The claim is well-formed and can be expressed formally
- The critical step (proving the one-to-one correspondence) is non-trivial
- Without this correspondence, the argument fails

## References

### Primary Sources

- **Original Claim**: Diaby, M. (2004). "P=NP: Linear Programming Formulation of the Traveling Salesman Problem"
  - Available at: http://www.business.uconn.edu/users/mdiaby/tsplp/
- **Revised Version**: Diaby, M. (2006). "The traveling salesman problem: A Linear programming formulation"
  - arXiv:cs/0609005 (multiple versions)

### Refutations

- **Hofman Counter-Example (2006)**: Hofman, R. (2006). "Report on article: P=NP Linear programming formulation of the Traveling Salesman Problem"
  - arXiv:cs/0610125
- **Recent Counter-Example (2025)**: Hofman, R. (2025). "Counter-Example to Diaby's et al. Linear Programming Solution to the Traveling Salesman Problem"
  - Complexity Journal, DOI: 10.1155/cplx/3672180

### Diaby's Responses

- Diaby, M. (2006). "On 'P = NP: Linear Programming Formulation of the Traveling Salesman Problem': A reply to Hofman's Claim of a 'Counter-Example'"
  - arXiv:cs/0611074

### Context

- **Woeginger's List**: Entry #14
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Discussion Forum**: comp.theory newsgroup
  - Extensive discussions about the correctness of the proof

## Key Lessons

1. **LP vs ILP Distinction**: The difference between linear programming and integer linear programming is fundamental
2. **Proof Obligations**: Claiming that a formulation has certain properties requires rigorous proof
3. **Structural Correspondence**: Just because two problems seem related doesn't mean their solution spaces are in one-to-one correspondence
4. **The Power of Counter-Examples**: A single counter-example can refute a universal claim
5. **Persistence of Error**: Even after refutation, incorrect proofs can persist if the error is subtle

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches to P vs NP
- [Repository README](../../../README.md) - Overview of the P vs NP problem
