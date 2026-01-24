# Sergey Gubin (2006) - Original Proof Idea

## Overview

Sergey Gubin's 2006 paper claims to prove **P = NP** through two main approaches:

1. **ATSP/LP Approach**: A polynomial-sized linear programming formulation of the Asymmetric Traveling Salesman Problem (ATSP)
2. **SAT Reduction Approach**: A polynomial-time reduction from SAT to 2-SAT

## The Claim

Gubin asserted: "The ATSP polytope can be expressed by asymmetric polynomial size linear program."

If correct, this would imply that ATSP (and by extension all NP-complete problems) can be solved in polynomial time, proving P = NP.

## Core Approach 1: ATSP via Linear Programming

### The Idea

Gubin proposed an LP formulation for ATSP where:
1. The LP has polynomial size (O(n²) variables and constraints for n cities)
2. All extreme points of the LP polytope are claimed to be integral
3. These integral extreme points correspond to valid ATSP tours

### Why This Would Prove P = NP

If the LP formulation were correct:
- LP can be solved in polynomial time (Karmarkar 1984)
- ATSP tours would correspond to LP extreme points
- Therefore, ATSP could be solved in polynomial time
- Since ATSP is NP-complete, this implies P = NP

### The Error (Hofman 2006)

Hofman demonstrated that the LP formulation has **non-integral extreme points** that do not correspond to valid tours. The polynomial-sized LP does not maintain the required correspondence between extreme points and Hamiltonian cycles.

## Core Approach 2: SAT to 2-SAT Reduction

### The Idea

Gubin also proposed:
1. A polynomial-time reduction from general SAT to 2-SAT
2. Since 2-SAT is solvable in polynomial time, SAT would also be polynomial

### Why This Would Prove P = NP

If the reduction were correct:
- 2-SAT ∈ P (Krom 1967, Aspvall-Plass-Tarjan 1979)
- SAT reduces to 2-SAT in polynomial time (claimed)
- Therefore SAT ∈ P
- Since SAT is NP-complete, this implies P = NP

### The Error (Christopher, Huo, Jacobs 2008)

The reduction from SAT to 2-SAT has **exponential blowup** in the number of clauses. Converting a k-SAT clause to 2-SAT typically requires introducing exponentially many clauses or variables, making the reduction non-polynomial.

## Technical Details

### ATSP Formulation Structure

Gubin's LP formulation used:
- Variables: x_{ij} for each directed edge (i,j)
- Constraints: flow conservation, subtour elimination
- Size: O(n²) for n cities

The critical claim was that all vertices of this polytope are 0-1 integral.

### SAT Reduction Structure

The proposed reduction:
1. Takes a CNF formula with arbitrary clause sizes
2. Transforms to an equivalent 2-CNF formula
3. Claims polynomial size increase

The critical claim was that this transformation preserves satisfiability with polynomial blowup.

## References

### Original Paper
- Gubin, S. (2006). "A Polynomial Time Algorithm for The Traveling Salesman Problem"
  - arXiv:cs/0610042
  - Presented at 22nd Mountain West Conference on Combinatorics (2008)

### Refutations
- Hofman (2006). "Report on article: P=NP"
  - arXiv:cs/0610125
  - Counter-examples showing non-integral extreme points

- Christopher, I., Huo, D., & Jacobs, B. (2008). "Critique of Gubin's SAT Solver"
  - arXiv:0804.2699
  - Shows exponential blowup in SAT to 2-SAT reduction

### Background
- Woeginger's P vs NP List, Entry #33
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
