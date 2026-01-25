# Khadija Riaz & Malik Sikander Hayat Khiyal (2006) - P=NP via Polynomial-Time Hamiltonian Cycle Algorithm

**Attempt ID**: 38 (from Woeginger's list)
**Authors**: Khadija Riaz & Malik Sikander Hayat Khiyal
**Year**: 2006
**Claim**: P = NP
**Status**: Refuted
**Issue**: #443

---

## Summary

In 2006, Khadija Riaz and Malik Sikander Hayat Khiyal published a paper titled "Finding Hamiltonian Cycle in Polynomial Time" in Information Technology Journal (Volume 5, pages 851-859). They claimed to have developed a polynomial-time algorithm for finding Hamiltonian cycles in graphs, which would prove P = NP since the Hamiltonian Cycle Problem is NP-complete.

The approach combines preprocessing conditions, degree-based greedy selection, and limited backtracking. The authors claim this reduces the exponential complexity of exhaustive search to polynomial time.

---

## Directory Structure

```
riaz-khiyal-2006-peqnp/
├── README.md                           # This file - overview of the attempt
├── ORIGINAL.md                         # Original paper text converted to Markdown
├── proof/                              # Forward formalization of the proof attempt
│   ├── README.md                       # Documentation of proof formalizations
│   ├── lean/
│   │   └── RiazKhiyalProof.lean       # Lean 4 formalization
│   └── rocq/
│       └── RiazKhiyalProof.v          # Rocq formalization
└── refutation/                         # Refutation demonstrating why the proof fails
    ├── README.md                       # Documentation of refutations
    ├── lean/
    │   └── RiazKhiyalRefutation.lean  # Lean 4 refutation
    └── rocq/
        └── RiazKhiyalRefutation.v     # Rocq refutation
```

**Notes**:
- Isabelle formalizations have been archived in `/archive/isabelle/riaz-khiyal-2006-peqnp/` following the repository's sunset of Isabelle support (see #530)
- ORIGINAL.pdf is not available due to access restrictions on the publisher's website

---

## Main Argument

### The Approach

1. **Preprocessing Phase**: Eliminate graphs that cannot contain Hamiltonian cycles
   - Remove parallel edges and self-loops
   - Reject graphs where any node has degree 1
   - Reject graphs where any node has more than two adjacent degree-2 nodes

2. **Greedy Selection with Limited Backtracking**:
   - Start from the highest-degree node
   - Select next nodes by prioritizing "least degree" neighbors
   - Store potential backtrack points in a "junction stack"
   - Backtrack only at "junction nodes" when necessary

3. **Claimed Polynomial Complexity**: The authors assert that backtracking occurs only at polynomially-many junction nodes, limiting total time to polynomial.

### Key Technical Claim

> "Backtracking may occur only on the junction nodes"

This claim is central to the polynomial-time complexity assertion but lacks formal proof in the paper.

---

## The Errors

### 1. Missing Complexity Analysis

**The Error**: The paper provides no formal time complexity proof or mathematical analysis.

**Why This Matters**:
- Claims like "backtracking is limited" are presented as intuitions, not proven theorems
- The phrase "few nodes are junction nodes" lacks any formal definition or worst-case bound
- Without rigorous complexity analysis, there is no proof of polynomial time

### 2. Incomplete Algorithmic Details

**The Error**: Critical algorithmic details are missing or incomplete.

**Specific Issues**:
- Step 5 of the algorithm contains placeholder text where actual selection logic should appear
- The "valid selection conditions" mentioned are never formally defined
- The exact criteria for "junction nodes" are unclear
- The backtracking mechanism is not rigorously specified

### 3. No Proof of Correctness

**The Error**: The paper does not prove that the algorithm finds Hamiltonian cycles in all graphs that have them.

**Why This Matters**:
- Greedy algorithms with limited backtracking are known to fail on certain graph structures
- Without a correctness proof, there's no guarantee the algorithm solves the problem

### 4. Circular Reasoning About Complexity

**The Error**: The authors argue the problem is tractable because they have "valid selection conditions," but don't prove these conditions guarantee polynomial termination.

**The Circular Logic**:
1. "We have valid selection conditions" (unproven)
2. "These conditions limit backtracking" (unproven)
3. "Therefore the algorithm is polynomial" (conclusion without proof)

### 5. No Engagement with NP-Completeness Theory

**The Error**: The paper makes no attempt to explain why their approach circumvents the fundamental barriers of NP-completeness.

**Why This Matters**:
- Thousands of researchers have attempted greedy approaches to NP-complete problems
- The paper doesn't address why their approach succeeds where others have failed
- No formal complexity argument demonstrates how the approach bypasses the P vs NP barrier

---

## Known Counter-Examples

### Worst-Case Graphs for Greedy Algorithms

1. **Regular Graphs**: Graphs where all vertices have the same degree provide no guidance for degree-based heuristics
2. **Graph Families with Hidden Structure**: Certain graph families appear locally tractable but require global reasoning
3. **Adversarial Constructions**: Graphs can be constructed where greedy choices lead to dead ends, requiring exponential backtracking

### The Backtracking Problem

The claim that "backtracking occurs only on junction nodes" is false for general graphs:
- In the worst case, the number of junction nodes can be linear (or worse) in graph size
- Each junction node may have multiple alternatives to explore
- The combination of multiple junction nodes with multiple choices leads to exponential search spaces

---

## Formalization Structure

### ORIGINAL.md
Contains the original paper text converted to Markdown:
- Full text of the paper reconstructed from available sources
- Metadata and access information
- Algorithm description and key claims

### proof/
Formalizes what the authors **claimed to prove**:
- Algorithm structure and definitions
- Key claims (correctness, polynomial complexity, limited backtracking)
- Logical implications: IF claims hold THEN P = NP
- **Gaps explicitly marked** with `sorry` (Lean) and `Admitted` (Rocq)

### refutation/
Demonstrates why the claims **cannot hold**:
- Counter-example constructions
- Proofs that greedy algorithms can fail
- Demonstrations that backtracking can be exponential
- Refutation of the paper's conclusion

---

## Key Lessons

1. **Proof Obligations Are Non-Negotiable**: Claiming polynomial-time complexity requires rigorous proof, not intuition
2. **Heuristics vs. Algorithms**: Working well in practice doesn't mean working in all cases
3. **Completeness Matters**: An algorithm must handle worst-case inputs, not just typical ones
4. **The Hardness of NP-Completeness**: Simple greedy approaches have been tried countless times; the difficulty lies in handling adversarial cases
5. **Rigor in Computer Science**: Informal arguments and missing details are red flags in complexity theory
6. **The Burden of Extraordinary Claims**: Solving P vs NP requires extraordinary evidence, including complete algorithmic details and rigorous proofs

---

## Historical Context

This attempt follows a common pattern in P vs NP attempts:
1. Choose an NP-complete problem with a simple statement (Hamiltonian Cycle)
2. Develop a greedy or heuristic approach
3. Observe it works well on small examples
4. Claim polynomial complexity without rigorous proof
5. Fail to address worst-case behavior

Similar flawed attempts have been made for:
- Traveling Salesman Problem (numerous attempts)
- Graph Coloring (many greedy approaches)
- Boolean Satisfiability (countless heuristics)
- Vertex Cover (various approximation schemes misunderstood as exact algorithms)

---

## References

### Primary Source

- **Original Paper**: Riaz, K., & Khiyal, M. S. H. (2006). "Finding Hamiltonian Cycle in Polynomial Time"
  - Information Technology Journal, Volume 5, pages 851-859
  - DOI: 10.3923/itj.2006.851.859
  - Available at: https://scialert.net/fulltext/?doi=itj.2006.851.859
  - ResearchGate: https://www.researchgate.net/publication/26556773_Finding_Hamiltonian_Cycle_in_Polynomial_Time

### Background on Hamiltonian Cycle Problem

- **Karp's 21 NP-Complete Problems**: Karp, R. M. (1972). "Reducibility Among Combinatorial Problems"
  - Hamiltonian Cycle was one of the original 21 problems proven NP-complete

- **Garey & Johnson**: "Computers and Intractability: A Guide to the Theory of NP-Completeness" (1979)
  - Section on Hamiltonian problems and their complexity

### Context

- **Woeginger's List**: Entry #38
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Related Issue**: #443 in this repository

---

## Building the Formalizations

### Lean 4
```bash
cd proof/lean/
lean RiazKhiyalProof.lean

cd ../../refutation/lean/
lean RiazKhiyalRefutation.lean
```

### Rocq (Coq)
```bash
cd proof/rocq/
rocqc RiazKhiyalProof.v

cd ../../refutation/rocq/
rocqc RiazKhiyalRefutation.v
```

---

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Repository README](../../../README.md) - Overview of the P vs NP problem
- [Contributing Guidelines](../../../CONTRIBUTING.md) - How to contribute formalizations
- [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) - Comprehensive list of P vs NP attempts
