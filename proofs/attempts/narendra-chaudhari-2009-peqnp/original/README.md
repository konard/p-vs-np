# Narendra S. Chaudhari (2009) - Original Proof Idea

## The Claim

Narendra S. Chaudhari claimed to prove **P=NP** by presenting a polynomial time algorithm (O(n^13)) for the 3-SAT problem using a clause-based representation approach.

## Core Approach

### Step 1: Define a Clause-Based Representation

Chaudhari proposed representing 3-SAT problems using clauses as the fundamental computational units instead of literals. The key innovation claimed was:

- Traditional approaches work with literals (variables and their negations) as primary units
- Chaudhari's approach uses **clauses** (disjunctions of 3 literals) as primary units
- This representation shift is claimed to enable polynomial time solving

### Step 2: Develop O(n^13) Algorithm

The paper claimed to present an algorithm that solves 3-SAT in polynomial time:

1. Convert the 3-SAT instance to the clause-based representation
2. Apply the algorithm using clauses as computational units
3. Determine satisfiability in O(n^13) time where n is the number of variables

### Step 3: Conclude P=NP

Since 3-SAT is NP-complete (Cook-Levin Theorem, 1971):
- Any polynomial time algorithm for 3-SAT would imply P=NP
- The claimed O(n^13) algorithm is polynomial
- Therefore, P=NP

## Why This Approach Seemed Promising

The clause-based representation approach had intuitive appeal:

1. **Different perspective**: Looking at the problem from a clause-centric view rather than a variable-centric view
2. **Structural insight**: Clauses capture the constraint structure directly
3. **Prior work**: Some SAT solving techniques do focus on clause structure (DPLL, CDCL)

## The Fundamental Problem

However, this approach fails because:

1. **Representation equivalence**: Any valid representation must encode the same information
   - A 3-SAT instance with n variables and m clauses requires Θ(m) space
   - The difficulty of the problem is preserved across representations

2. **The exponential mapping claim**: According to Woeginger's list:
   > "The mapping from literals to clauses is exponential while from clauses to 3-SAT is linear."

   This statement suggests:
   - There are O(n³) possible 3-clauses over n variables
   - But a 3-SAT instance only uses m of these (typically m = O(n))
   - The existence of exponentially many potential clauses does not help solve the problem

3. **Hidden complexity**: If the algorithm truly runs in O(n^13) time, then either:
   - It does NOT correctly solve all 3-SAT instances (incompleteness), OR
   - The representation conversion actually requires exponential time/space, OR
   - The algorithm is incorrect for some inputs

4. **No rigorous proof**: The paper likely lacks:
   - Rigorous proof that the algorithm correctly handles ALL 3-SAT instances
   - Complete complexity analysis including representation conversion costs
   - Verification for edge cases and pathological instances

## The Dilemma

This approach faces the fundamental dilemma of representation-based approaches:

1. If the clause-based representation captures all information needed to solve 3-SAT:
   - Then it must preserve the computational difficulty
   - No simplification is achieved

2. If the representation loses information:
   - Then the algorithm cannot correctly solve all instances
   - The approach is incomplete

## Historical Context

This attempt is part of a broader pattern of P=NP claims based on:
- Representation changes (literals vs clauses, graphs vs matrices, etc.)
- Belief that changing how we VIEW a problem changes its DIFFICULTY
- Lack of rigorous verification of correctness and complexity claims

## The Paper

- **Title**: "Computationally Difficult Problems: Some Investigations"
- **Author**: Narendra S. Chaudhari
- **Publication**: Journal of the Indian Academy of Mathematics, Vol. 31, 2009, pages 407-444
- **Status**: Appears in Woeginger's list as Entry #59

## References

- Woeginger's P vs NP page, Entry #59
- Cook, S. A. (1971). "The complexity of theorem proving procedures"
- Karp, R. M. (1972). "Reducibility among combinatorial problems"
