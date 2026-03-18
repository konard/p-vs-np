# Delacorte/Czerwinski (2007) - P=NP/PSPACE via Graph Isomorphism

**Attempt ID**: 41 (from Woeginger's list)
**Authors**: Matthew Delacorte / Reiner Czerwinski
**Year**: 2007
**Claim**: P = PSPACE (and consequently P = NP)
**Status**: Refuted (both papers contain fundamental errors)

## Summary

In 2007, two separate papers emerged making contradictory claims about the computational complexity of the Graph Isomorphism (GI) problem:

1. **Matthew Delacorte** (August 2007): Claimed to prove that Graph Isomorphism is PSPACE-complete
2. **Reiner Czerwinski** (November 2007): Claimed to prove that Graph Isomorphism is in P (solvable in polynomial time)

Together, if both claims were correct, they would imply P = PSPACE (and consequently P = NP). However, both claims contain fundamental errors, and this entry represents a notable example of conflicting "proofs" rather than a coordinated attempt.

## Background: Graph Isomorphism Problem

### Definition

The **Graph Isomorphism Problem** asks: Given two graphs G and H, determine whether they are isomorphic (i.e., whether there exists a bijection between their vertices that preserves adjacency).

### Known Complexity Status

- **NOT known to be NP-complete**: Despite being in NP, GI is not believed to be NP-complete
- **NOT known to be in P**: No polynomial-time algorithm is known (as of 2007)
- **Quasi-polynomial algorithm**: In 2015, László Babai announced a quasi-polynomial time algorithm
- **Between P and NP-complete**: GI is considered to be in an intermediate complexity class

### Significance

GI is one of the few natural problems in NP that is:
- Not known to be in P
- Not known to be NP-complete
- A candidate for an intermediate complexity class (if P ≠ NP)

## Delacorte's Claim: GI is PSPACE-complete

### The Argument

Delacorte's paper "Graph Isomorphism is PSPACE-complete" (August 2007) claimed:

1. Graph Isomorphism is PSPACE-complete
2. Since GI is in NP, this would imply NP = PSPACE
3. Combined with Czerwinski's later claim, this would give P = PSPACE

### Why This Would Matter

If GI were PSPACE-complete:
- Since GI ∈ NP, we would have PSPACE ⊆ NP
- But we already know NP ⊆ PSPACE
- Therefore: NP = PSPACE
- This would be a major breakthrough, though not necessarily proving P = NP

### The Error: Implausibility and Lack of Rigor

**Critical Issues**:

1. **Contradicts Strong Evidence**: The computational complexity community has extensively studied GI and found no evidence it is NP-complete, let alone PSPACE-complete

2. **Consequences Too Strong**: If GI were PSPACE-complete, this would collapse the polynomial hierarchy, which is considered highly unlikely

3. **Reduction Direction**: To prove PSPACE-completeness, one must show:
   - GI is in PSPACE (known to be true)
   - Every problem in PSPACE reduces to GI in polynomial time

   The second part is extraordinarily difficult and the paper's approach is fundamentally flawed

4. **Technical Errors**: The paper reportedly contains errors in:
   - The construction of the reduction
   - Failure to preserve the polynomial-time requirement
   - Incorrect understanding of what PSPACE-completeness requires

## Czerwinski's Claim: GI is in P

### The Argument

Czerwinski's paper "A Polynomial Time Algorithm for Graph Isomorphism" (November 2007) claimed:

1. Presented an algorithm that solves Graph Isomorphism in polynomial time
2. Therefore GI ∈ P
3. Combined with Delacorte's claim, this would give P = PSPACE

### Why This Would Matter

If true, this would:
- Solve a decades-old open problem
- Resolve one of the major questions in computational complexity
- Provide practical benefits (GI has applications in chemistry, biology, pattern recognition)

### The Error: Incomplete or Incorrect Algorithm

**Critical Issues**:

1. **Failure to Handle All Cases**: The algorithm likely works correctly only on restricted classes of graphs, not on all graphs

2. **Incorrect Complexity Analysis**: Common errors in polynomial-time claims for GI include:
   - Failing to account for all steps in the algorithm
   - Incorrect analysis of recursive or iterative procedures
   - Hidden exponential factors in the analysis

3. **Counterexamples**: The algorithm can be tested on hard instances of GI (e.g., strongly regular graphs, random graphs with specific properties) where it likely fails to run in polynomial time

4. **Lack of Verification**: A correct polynomial-time algorithm for GI would:
   - Be verifiable by independent researchers
   - Have been accepted by the complexity theory community
   - Have received significant attention and awards (potentially a Gödel Prize)

   None of these occurred, indicating fundamental problems with the proof

## The Combined Claim: P = PSPACE

### Logical Structure

If both papers were correct:

1. GI is PSPACE-complete (Delacorte)
2. GI ∈ P (Czerwinski)
3. Therefore: Every PSPACE problem reduces to GI (by PSPACE-completeness)
4. Therefore: Every PSPACE problem is in P (by transitivity)
5. Conclusion: P = PSPACE

Since we know NP ⊆ PSPACE, this would also imply P = NP.

### Why This is Almost Certainly False

**Strong Evidence Against P = PSPACE**:

1. **Hierarchy Theorems**: Time and space hierarchy theorems show that giving more resources (time or space) allows solving strictly more problems
2. **Polynomial Hierarchy**: P = PSPACE would collapse the polynomial hierarchy to P
3. **Savitch's Theorem**: We know NSPACE(f(n)) ⊆ SPACE(f(n)²), but this doesn't give us P = PSPACE
4. **PSPACE-complete Problems**: Problems like TQBF (True Quantified Boolean Formula) appear fundamentally harder than anything in P

### The Nature of This "Attempt"

This entry is unusual because:
- It consists of **two contradictory papers** by different authors
- They were published months apart (not as a coordinated effort)
- The contradiction is **internal**: both cannot be correct simultaneously
- Even if the contradiction existed, it would only prove that at least one claim is wrong

This highlights an important point: contradictory "proofs" don't constitute evidence for anything except that at least one (and likely both) proofs are incorrect.

## Detailed Error Analysis

### Common Errors in GI Complexity Claims

**For PSPACE-completeness claims**:
- Incorrect reduction constructions
- Failure to maintain polynomial-time constraints in reductions
- Misunderstanding of what PSPACE-completeness requires

**For polynomial-time algorithm claims**:
- Algorithms that work only on special graph classes
- Incorrect runtime analysis hiding exponential factors
- Incomplete algorithms that don't handle all cases
- Heuristics that work well in practice but aren't guaranteed polynomial time

### Why GI is Difficult

The Graph Isomorphism problem is difficult because:

1. **Exponential search space**: There are n! possible vertex mappings to check
2. **Symmetry**: Graph automorphisms create multiple valid solutions
3. **No obvious structure**: Unlike many NP-complete problems, GI doesn't have clear structure to exploit
4. **Hardness results**: GI is hard for certain restricted cases, but we can't prove it's NP-complete

### What Would Be Needed for a Correct Proof

**For PSPACE-completeness**:
- A polynomial-time reduction from a known PSPACE-complete problem (like TQBF) to GI
- Proof that the reduction preserves the yes/no answer
- Verification that all steps are indeed polynomial time

**For polynomial time**:
- An algorithm with clearly bounded polynomial running time
- Proof of correctness on all graph instances
- Independent verification and implementation
- Analysis showing the algorithm handles worst-case inputs

## Formalization Goals

In this directory, we formalize:

1. **Graph Isomorphism Problem**: Formal definition of GI in theorem provers
2. **Complexity Classes**: Definitions of P, NP, and PSPACE
3. **Completeness Notions**: What it means for a problem to be PSPACE-complete
4. **The Contradiction**: Formal statement showing that both claims cannot be simultaneously true
5. **Why Each Claim is Implausible**: Formal evidence against each individual claim

The formalization demonstrates:
- The precise technical requirements for each claim
- Why these requirements are not met in the attempted proofs
- The logical structure of the combined claim
- Why the contradiction itself doesn't prove anything meaningful

## Broader Context

### Historical Perspective

GI has been extensively studied:
- **1970s-1980s**: Intensive research into GI complexity
- **Babai's Algorithm (1983)**: Moderately exponential time algorithm
- **2015**: Babai's quasi-polynomial time algorithm (later refined)
- **Still open**: Whether GI ∈ P remains unknown

### Lessons for P vs NP Research

This case illustrates several important points:

1. **Contradictory claims don't help**: Two wrong proofs don't make a right
2. **Complexity requires rigor**: Informal arguments about complexity are easily mistaken
3. **Community scrutiny**: Correct proofs must withstand peer review
4. **Intermediate complexity**: Not everything in NP is either in P or NP-complete
5. **Extraordinary claims require extraordinary evidence**: Claims about major complexity results need thorough verification

## References

### Primary Sources

- **Delacorte, M.** (August 2007). "Graph Isomorphism is PSPACE-complete"
- **Czerwinski, R.** (November 2007). "A Polynomial Time Algorithm for Graph Isomorphism"

*Note: These papers appear to have limited circulation and were not published in peer-reviewed venues*

### Context and Critique

- **Woeginger's List**: Entry #41
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Notes these as contradictory claims

### Graph Isomorphism Background

- **Babai, L.** (2016). "Graph Isomorphism in Quasipolynomial Time"
  - Proceedings of STOC 2016
  - arXiv:1512.03547
- **Köbler, J., Schöning, U., & Torán, J.** (1993). "The Graph Isomorphism Problem: Its Structural Complexity"
  - Birkhäuser, Boston
- **Zemlyachenko, V.N., Korneenko, N.M., & Tyshkevich, R.I.** (1985). "Graph Isomorphism Problem"
  - Journal of Soviet Mathematics, 29(4), 1426-1481

### Complexity Theory Background

- **Sipser, M.** (2012). "Introduction to the Theory of Computation" (3rd ed.)
  - Chapter on Space Complexity (PSPACE)
- **Arora, S., & Barak, B.** (2009). "Computational Complexity: A Modern Approach"
  - Chapter 4: Space Complexity

## Key Lessons

1. **Contradictions indicate errors**: When two proofs contradict each other, at least one is wrong
2. **PSPACE ≠ P is widely believed**: Strong theoretical evidence supports this separation
3. **GI is a special case**: Its apparent intermediate status makes it unsuitable for easy collapse arguments
4. **Polynomial time requires proof**: Claiming an algorithm is polynomial time requires rigorous analysis
5. **Completeness is subtle**: PSPACE-completeness requires specific types of reductions
6. **Publication ≠ Correctness**: Papers claiming major results need peer review and community acceptance

## See Also

- [P vs NP Framework](../../p_eq_np/) - General framework for evaluating P vs NP claims
- [PSPACE vs P](../../p_vs_np_undecidable/) - Approaches to separating complexity classes
- [Repository README](../../../README.md) - Overview of the P vs NP problem
