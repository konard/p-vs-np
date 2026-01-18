# Cynthia Ann Harlan Krieger & Lee K. Jones (2008) - P=NP via Polynomial Hamiltonian Circuit Detection

**Attempt ID**: 42 (from Woeginger's list)
**Authors**: Cynthia Ann Harlan Krieger & Lee K. Jones
**Year**: 2008
**Claim**: P = NP
**Status**: Refuted

## Summary

In 2008, Cynthia Ann Harlan Krieger and Lee K. Jones filed a patent application (US 2008/0071849) claiming to have developed a polynomial-time algorithm for detecting Hamiltonian circuits in undirected graphs. Since the Hamiltonian circuit problem is NP-complete, the authors claimed this proved P = NP. The patent application was based on provisional application No. 60/844,680 filed on September 15, 2006.

## Main Argument

### The Approach

1. **Target Problem**: The Hamiltonian circuit problem - determining whether a given undirected graph contains a cycle that visits each vertex exactly once
2. **Claimed Algorithm**: A polynomial-time algorithm for detecting the presence of a Hamiltonian circuit
3. **NP-Completeness**: The Hamiltonian circuit problem is a well-known NP-complete problem
4. **Claimed Implication**: Since any NP problem can be reduced to the Hamiltonian circuit problem in polynomial time, a polynomial-time solution to Hamiltonian circuits would imply P = NP

### Key Technical Claim

The patent application claimed:
- A "polynomial running time calculation" for detecting Hamiltonian circuits
- That this algorithm has polynomial time complexity in the size of the input graph
- That the existence of such an algorithm proves P = NP

The application stated: "With this polynomial running time calculation result given for detecting the presence of a Hamiltonian circuit in an undirected graph, it has been shown that P equals any known NP problem or NP."

## The Error

### Fundamental Issues

**The Error**: The patent application does not provide a valid polynomial-time algorithm for the Hamiltonian circuit problem.

Several critical problems exist with this claim:

### 1. Lack of Rigorous Algorithm Description

**Problem**: Patent applications have different standards than peer-reviewed mathematical proofs
- Patents are legal documents, not mathematical proofs
- Patent examiners are not required to verify the correctness of mathematical claims
- The algorithmic details provided do not constitute a rigorous proof of polynomial time complexity

**Why This Matters**:
- Extraordinary claims require extraordinary proof
- A proof of P = NP would require:
  - A complete, unambiguous algorithm specification
  - A rigorous proof that the algorithm is correct (produces the right answer)
  - A rigorous proof that the algorithm runs in polynomial time
  - Peer review by the theoretical computer science community

### 2. Confusion Between Problem Types

**Problem**: Claiming to solve a decision problem vs. actually solving it

The Hamiltonian circuit problem comes in different forms:
- **Decision Problem**: Does a Hamiltonian circuit exist? (Yes/No)
- **Search Problem**: Find a Hamiltonian circuit if one exists
- **Optimization Problem**: Find the shortest Hamiltonian circuit (TSP variant)

Many attempted "solutions" conflate these problems or provide algorithms that:
- Only work on special classes of graphs (not general graphs)
- Use exponential space or other resources while claiming polynomial time
- Have incorrect time complexity analysis

### 3. No Peer Review or Acceptance

**Problem**: The claim was never validated by the mathematical community

**Evidence of Non-Acceptance**:
- No publication in peer-reviewed computer science or mathematics journals
- No presentation at major conferences (STOC, FOCS, etc.)
- No verification by complexity theorists
- The P vs NP problem remains open (it's one of the seven Millennium Prize Problems with a $1 million reward)
- No subsequent citations in the theoretical computer science literature validating the claim

### 4. Patent Grants Are Not Mathematical Proofs

**Critical Distinction**:
- **Patent Examination**: Focuses on novelty, non-obviousness, and utility in a legal/practical sense
- **Mathematical Proof**: Requires logical rigor, completeness, and verification by experts
- Many patents contain mathematical claims that are incorrect or unproven
- The USPTO does not verify the correctness of complex mathematical proofs

### Common Pitfalls in Hamiltonian Circuit Algorithms

Attempted polynomial-time algorithms for NP-complete problems often fall into these traps:

1. **Hidden Exponential Steps**: The algorithm may have steps that appear polynomial but actually hide exponential complexity
2. **Special Cases**: The algorithm only works for specific types of graphs (e.g., planar graphs, bounded degree graphs) but is claimed to be general
3. **Incorrect Analysis**: The time complexity analysis contains errors or makes unjustified assumptions
4. **Incomplete Correctness**: The algorithm doesn't always produce the correct answer
5. **Non-Deterministic Steps**: The algorithm contains "guess" or "choose" operations that hide exponential search

## Why This Approach Cannot Work (Assuming P ≠ NP)

If P ≠ NP (as most complexity theorists believe), then:

1. **No Polynomial Algorithm Exists**: There cannot be a polynomial-time algorithm for Hamiltonian circuits
2. **Proof Structure**: Any claimed polynomial algorithm must have an error in either:
   - The algorithm specification (it doesn't actually solve the problem)
   - The correctness proof (it doesn't always give the right answer)
   - The complexity analysis (it actually takes exponential time)

## Broader Context

### Why These Claims Persist

Hamiltonian circuit attempts are common because:
- The problem has a simple, intuitive statement
- Small examples can be solved by hand easily
- The difficulty comes from scaling, which is hard to appreciate intuitively
- Graph traversal algorithms exist and may seem "close" to solving the problem

### The Verification Challenge

For P vs NP:
- A proof that P = NP requires a polynomial algorithm that the community can verify
- A proof that P ≠ NP requires showing no such algorithm can exist (much harder)
- Claimed proofs must survive intense scrutiny from expert complexity theorists
- The $1 million prize from the Clay Mathematics Institute ensures serious claims get examined

### Historical Pattern

This attempt follows a common pattern:
1. Author believes they've found a polynomial algorithm
2. Files patent or posts online (avoiding peer review)
3. Mathematical community doesn't validate the claim
4. No subsequent impact on theoretical computer science
5. P vs NP remains open

## Formalization Goals

In this directory, we formalize:

1. **The Hamiltonian Circuit Problem**: Precise definition as a decision problem
2. **What "Polynomial-Time Algorithm" Means**: Formal complexity class definitions
3. **NP-Completeness**: What it means for Hamiltonian circuits to be NP-complete
4. **The Implication**: Why a polynomial algorithm for any NP-complete problem implies P = NP
5. **The Gap**: Where the claimed proof fails (no verified polynomial algorithm provided)

The formalization demonstrates that:
- The problem is well-defined
- The claim, if true, would indeed prove P = NP
- The critical missing element is a verified polynomial-time algorithm
- Patent filing does not constitute mathematical proof

## References

### Primary Source

- **Patent Application**: Krieger, C.A.H. (2008). "Polynomial method for detecting a Hamiltonian circuit"
  - US Patent Application: 2008/0071849
  - Filed: September 14, 2007
  - Published: March 20, 2008
  - Available at: https://www.freepatentsonline.com/y2008/0071849.html
  - Based on Provisional Application: 60/844,680 (filed September 15, 2006)

### Background and Context

- **Woeginger's List**: Entry #42
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Hamiltonian Circuit Problem**
  - Classic NP-complete problem
  - See: Karp, R. (1972). "Reducibility Among Combinatorial Problems"
- **P vs NP Problem**
  - Clay Mathematics Institute Millennium Prize Problem
  - https://www.claymath.org/millennium-problems/p-vs-np-problem

### Why Patents Are Not Proofs

- **USPTO Patent Examination**: Focuses on legal requirements, not mathematical verification
- **Mathematical Proof Standards**: Require peer review and community consensus
- **Historical Examples**: Many patents contain unverified or incorrect mathematical claims

### NP-Completeness Theory

- **Cook-Levin Theorem**: First NP-complete problem (SAT)
- **Karp's 21 Problems**: Including Hamiltonian circuit
- **Reductions**: How NP-complete problems relate to each other

## Key Lessons

1. **Patent ≠ Proof**: Legal patent grants do not constitute mathematical validation
2. **Peer Review Matters**: Extraordinary claims require verification by domain experts
3. **Complexity Analysis Is Subtle**: Apparent polynomial algorithms often hide exponential complexity
4. **Problem Specifications**: Important to distinguish decision, search, and optimization versions
5. **Burden of Proof**: The claimant must provide complete algorithm and rigorous analysis
6. **Community Validation**: Major results in mathematics require acceptance by the research community

## Why This Matters

The P vs NP problem is fundamental to:
- **Cryptography**: Many encryption schemes rely on the assumption that P ≠ NP
- **Optimization**: Understanding the limits of efficient computation
- **Algorithm Design**: Knowing which problems have efficient solutions
- **Philosophy of Computer Science**: Understanding the nature of computation itself

Incorrect claims, even when filed as patents, do not change the underlying mathematical reality. The problem remains open and continues to be one of the most important questions in computer science and mathematics.

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches to P vs NP
- [Repository README](../../../README.md) - Overview of the P vs NP problem
- [Other Hamiltonian Circuit Attempts](../) - Related attempts on Woeginger's list
