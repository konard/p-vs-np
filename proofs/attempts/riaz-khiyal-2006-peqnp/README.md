# Khadija Riaz & Malik Sikander Hayat Khiyal (2006) - P=NP via Polynomial-Time Hamiltonian Cycle Algorithm

**Attempt ID**: 38 (from Woeginger's list)
**Authors**: Khadija Riaz & Malik Sikander Hayat Khiyal
**Year**: 2006
**Claim**: P = NP
**Status**: Refuted

## Summary

In 2006, Khadija Riaz and Malik Sikander Hayat Khiyal published a paper titled "Finding Hamiltonian Cycle in Polynomial Time" in Information Technology Journal (Volume 5, pages 851-859). They claimed to have developed a polynomial-time algorithm for finding Hamiltonian cycles in graphs, which would prove P = NP since the Hamiltonian Cycle Problem is NP-complete.

## Main Argument

### The Approach

1. **Problem Selection**: The authors chose to tackle the Hamiltonian Cycle Problem (HCP), a well-known NP-complete problem
2. **Greedy Algorithm with Limited Backtracking**: They proposed a greedy selection method with restricted backtracking
3. **Degree-Based Heuristics**: The algorithm prioritizes node selection based on vertex degrees
4. **Claimed Polynomial Complexity**: They asserted that their backtracking strategy limits the search space to polynomial size

### Algorithm Structure

The proposed algorithm consists of three main phases:

1. **Preprocessing Phase**:
   - Remove parallel edges and self-loops
   - Reject graphs where any node has degree 1
   - Reject graphs where any node has more than two adjacent degree-2 nodes

2. **Processing Phase**:
   - Start from the highest-degree node
   - Select next nodes by prioritizing "least degree" neighbors
   - Store potential backtrack points in a "junction stack"
   - Backtrack only at "junction nodes" when necessary

3. **Verification Phase**:
   - Check if the constructed path forms a valid Hamiltonian cycle

### Key Technical Claim

The crucial claim was that by using degree-based heuristics, **"backtracking may occur only on the junction nodes"**, which would allegedly reduce the complexity from exponential to polynomial time.

## The Errors

### 1. Missing Complexity Analysis

**The Error**: The paper provides no formal time complexity proof or mathematical analysis.

**Why This Matters**:
- Claims like "backtracking is limited" are presented as intuitions, not proven theorems
- The phrase "few nodes are junction nodes" lacks any formal definition or worst-case bound
- Without a rigorous complexity analysis, there is no proof that the algorithm runs in polynomial time
- The number of junction nodes could potentially be proportional to the total number of nodes in the worst case

### 2. Incomplete Algorithmic Details

**The Error**: Critical algorithmic details are missing or incomplete in the paper.

**Specific Issues**:
- Step 5 of the algorithm contains placeholder text where actual selection logic should appear
- The "valid selection conditions" mentioned are never formally defined
- The exact criteria for what constitutes a "junction node" are unclear
- The backtracking mechanism is not rigorously specified

**Why This Matters**:
- Without complete algorithmic details, the approach cannot be verified or refuted through implementation
- Missing details suggest the authors may not have fully worked out the algorithm
- Incomplete specifications make it impossible to analyze the true complexity

### 3. No Proof of Correctness

**The Error**: The paper does not prove that the algorithm finds Hamiltonian cycles in all graphs that have them.

**Why This Matters**:
- Even if the algorithm were polynomial-time, it would be useless if it doesn't always find the solution when one exists
- Greedy algorithms with limited backtracking are known to fail on certain graph structures
- Without a correctness proof, there's no guarantee the algorithm solves the problem

### 4. Circular Reasoning About Complexity

**The Error**: The authors argue the problem is tractable because they have "valid selection conditions," but don't prove these conditions guarantee polynomial termination.

**The Circular Logic**:
1. "We have valid selection conditions" (unproven)
2. "These conditions limit backtracking" (unproven)
3. "Therefore the algorithm is polynomial" (conclusion without proof)

**Why This Matters**:
- This is a logical fallacy: assuming what needs to be proven
- The existence of "valid conditions" is precisely what needs rigorous mathematical proof
- Many NP-complete problems have greedy heuristics that work well in practice but fail in the worst case

### 5. False Dichotomy About Search Strategies

**The Error**: The paper presents a false choice between exhaustive search (exponential) and their greedy approach (claimed polynomial), ignoring the need to prove their approach handles all cases.

**Why This Matters**:
- Just because you avoid exhaustive search doesn't mean you've achieved polynomial time
- The hardness of NP-complete problems comes from the need to explore exponentially many possibilities in the worst case
- Any correct polynomial-time algorithm would need to prove it never encounters such worst cases

### 6. No Engagement with NP-Completeness Theory

**The Error**: The paper makes no attempt to explain why their approach circumvents the fundamental barriers of NP-completeness.

**Why This Matters**:
- Thousands of researchers have attempted to find polynomial algorithms for NP-complete problems
- The paper doesn't address why their approach succeeds where others have failed
- No formal reduction or complexity argument demonstrates how their approach bypasses the P vs NP barrier
- The existence of NP-completeness reductions means that if this algorithm worked, it would solve ALL NP-complete problems in polynomial time

## Known Counter-Examples and Refutations

### Worst-Case Graphs for Greedy Algorithms

Greedy degree-based algorithms are known to fail on certain graph structures:

1. **Regular Graphs**: Graphs where all vertices have the same degree provide no guidance for degree-based heuristics
2. **Graph Families with Hidden Structure**: Certain graph families appear locally tractable but require global reasoning
3. **Adversarial Constructions**: Graphs can be constructed where greedy choices lead to dead ends, requiring exponential backtracking

### The Backtracking Problem

The key claim that "backtracking occurs only on junction nodes" is false for general graphs:
- In the worst case, the number of junction nodes can be linear (or worse) in the graph size
- Each junction node may have multiple alternatives to explore
- The combination of multiple junction nodes with multiple choices leads to exponential search spaces
- No mechanism in the algorithm prevents this exponential explosion

## Broader Context

### Why This Approach Is Tempting

The approach is appealing because:
- Greedy algorithms with limited backtracking work well for many practical instances
- Degree-based heuristics provide intuitive guidance for path construction
- The Hamiltonian Cycle Problem has a simple statement and seems amenable to clever tricks
- Many hard problems can be solved efficiently on restricted graph classes

### The Critical Distinction: Heuristics vs. Algorithms

- **Heuristics**: Methods that work well in practice but may fail on some inputs (polynomial-time heuristics exist for NP-complete problems)
- **Algorithms**: Guaranteed methods that always produce correct answers (no polynomial-time algorithms known for NP-complete problems unless P = NP)
- **The Gap**: The paper conflates a potentially useful heuristic with a proven algorithm

The authors' error was in claiming that their greedy heuristic is a polynomial-time algorithm without providing adequate proofs of:
1. Correctness (finds cycles when they exist)
2. Completeness (never misses a cycle)
3. Polynomial complexity (terminates in polynomial time in all cases)

### Historical Context

This attempt follows a common pattern in P vs NP attempts:
1. Choose an NP-complete problem with a simple statement
2. Develop a greedy or heuristic approach
3. Observe it works well on small examples
4. Claim polynomial complexity without rigorous proof
5. Fail to address worst-case behavior

Similar flawed attempts have been made for:
- Traveling Salesman Problem (numerous attempts)
- Graph Coloring (many greedy approaches)
- Boolean Satisfiability (countless heuristics)
- Vertex Cover (various approximation schemes misunderstood as exact algorithms)

## Formalization Goals

In this directory, we formalize:

1. **The Basic Problem**: What it means to find a Hamiltonian cycle in polynomial time
2. **The Algorithm Structure**: The general approach of greedy selection with limited backtracking
3. **The Critical Gaps**: Where the proof fails (missing complexity analysis, correctness proof, and completeness proof)
4. **Why This Would Imply P = NP**: If the algorithm were correct and polynomial-time
5. **The Refutation**: Why greedy approaches don't guarantee polynomial complexity for all graphs

The formalization demonstrates that:
- The problem is well-formed and NP-complete
- A polynomial-time algorithm would indeed prove P = NP
- The proposed algorithm lacks the necessary proofs for correctness, completeness, and polynomial complexity
- The backtracking claim is unsubstantiated and likely false in the worst case

## References

### Primary Source

- **Original Paper**: Riaz, K., & Khiyal, M. S. H. (2006). "Finding Hamiltonian Cycle in Polynomial Time"
  - Information Technology Journal, Volume 5, pages 851-859
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
- **Related**: Issue #44 in the repository

## Key Lessons

1. **Proof Obligations Are Non-Negotiable**: Claiming an algorithm is polynomial-time requires rigorous proof, not intuition
2. **Heuristics vs. Algorithms**: Working well in practice doesn't mean working in all cases
3. **Completeness Matters**: An algorithm must handle worst-case inputs, not just typical ones
4. **The Hardness of NP-Completeness**: Simple greedy approaches have been tried countless times; the difficulty lies in handling adversarial cases
5. **Rigor in Computer Science**: Informal arguments and missing details are red flags in complexity theory
6. **The Burden of Extraordinary Claims**: Solving P vs NP requires extraordinary evidence, including complete algorithmic details and rigorous proofs

## See Also

- [P = NP Framework](../../p_eq_np/) - General framework for evaluating P = NP claims
- [Hamiltonian Cycle Complexity](../../experiments/) - Experimental approaches to Hamiltonian problems
- [Repository README](../../../README.md) - Overview of the P vs NP problem
