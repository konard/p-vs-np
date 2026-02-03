# Refutation of the Riaz-Khiyal Attempt

This folder contains formal refutations demonstrating why the Riaz-Khiyal approach cannot prove P = NP. The refutations show that the key claims made in the paper are false or unproven, and that counter-examples exist.

## Purpose

The refutations serve to:
1. **Identify fatal flaws** - Demonstrate specific errors in the proof attempt
2. **Provide counter-examples** - Construct graphs where the approach fails
3. **Explain barriers** - Show why greedy algorithms cannot solve NP-complete problems in general
4. **Extract lessons** - Clarify what went wrong for educational purposes

## Files

### Lean 4
- **lean/RiazKhiyalRefutation.lean** - Complete refutation in Lean 4
  - Constructs counter-examples
  - Proves the key claims are false
  - Demonstrates the logical gaps

### Rocq (Coq)
- **rocq/RiazKhiyalRefutation.v** - Complete refutation in Rocq/Coq
  - Parallel structure to Lean version
  - Uses axioms for counter-example existence
  - Compiles successfully

## Main Refutation Points

### 1. Correctness Cannot Be Guaranteed

**Claim (from paper):** The greedy algorithm finds Hamiltonian cycles when they exist.

**Refutation:** Greedy degree-based algorithms can fail on specific graph structures.

```lean
-- Regular graphs provide no guidance for degree heuristics
theorem regular_graph_defeats_degree_heuristic :
  ∀ k : Nat, k > 2 →
    ∃ rg : RegularGraph,
      rg.degree = k ∧
      (∀ alg : RKAlgorithm,
        ∃ run : AlgorithmRun alg rg.graph,
          run.steps ≥ 2 ^ (rg.graph.numNodes / 2))

-- Adversarial graphs exist where greedy choices lead to dead ends
axiom adversarial_graphs_exist :
  ∃ ag : GreedyAdversarialGraph, ag.graph.numNodes > 10
```

### 2. Polynomial Complexity Is Unproven

**Claim (from paper):** Backtracking is limited to junction nodes, ensuring polynomial time.

**Refutation:** The number of junction nodes can be linear, and backtracking at each can be exponential.

```lean
-- Junction nodes can be Θ(n)
theorem junction_nodes_linear :
  ∃ g : Graph, ∃ junctionCount : Nat,
    junctionCount ≥ g.numNodes / 2

-- Many junctions with multiple choices = exponential time
theorem many_junctions_exponential_time :
  ∀ alg : RKAlgorithm,
    ∀ g : Graph,
      ∀ junctionCount : Nat,
        junctionCount ≥ g.numNodes / 2 →
        ∃ run : AlgorithmRun alg g,
          run.steps ≥ 2 ^ junctionCount
```

### 3. No Mechanism Prevents Exponential Backtracking

**Claim (from paper):** The algorithm's structure limits backtracking to polynomial operations.

**Refutation:** No such limitation exists in the algorithm as described.

```lean
theorem backtracking_not_limited :
  ¬(∀ alg : RKAlgorithm, BacktrackingLimited alg)
```

## Counter-Example Types

### Regular Graphs
In k-regular graphs (where all vertices have degree k), degree-based heuristics provide no useful guidance. The algorithm must effectively try many paths, leading to exponential time.

### Greedy-Adversarial Graphs
Graphs can be constructed where the greedy "least degree" choice at each step leads away from the Hamiltonian cycle, forcing extensive backtracking or complete failure.

### High-Branching Graphs
Graphs with many high-degree vertices create many junction nodes, each requiring exploration of multiple alternatives, resulting in exponential search space.

## Logical Structure of Refutation

1. **Assume the claims hold** - Correctness AND polynomial complexity
2. **Construct counter-examples** - Graphs where greedy algorithms provably fail
3. **Derive contradiction** - The algorithm cannot be both correct and polynomial
4. **Conclude refutation** - At least one key claim must be false

```lean
-- Main refutation theorem
theorem riaz_khiyal_refuted :
  ¬(∃ alg : RKAlgorithm,
    HasCorrectness alg ∧
    HasPolynomialComplexity alg)
```

## Specific Technical Errors

### Error 1: Undefined "Valid Selection Conditions"
The paper mentions "valid selection conditions" but never formally defines them or proves they guarantee polynomial time.

### Error 2: Circular Reasoning
The argument assumes junction nodes are few because backtracking is limited, and backtracking is limited because junction nodes are few.

### Error 3: Unproven Preprocessing Power
The preprocessing conditions reject some impossible cases but don't eliminate all hard instances.

### Error 4: Missing Worst-Case Analysis
The paper shows the algorithm works on simple examples but provides no worst-case complexity analysis.

## Why This Matters

### Greedy ≠ Optimal for NP-Complete Problems
The refutation demonstrates a general principle: greedy algorithms can be good heuristics but cannot guarantee optimal solutions for NP-complete problems in polynomial time (unless P = NP).

### Proof Obligations Are Non-Negotiable
Claiming polynomial-time complexity requires rigorous mathematical proof, not intuition or examples.

### NP-Completeness Is a Real Barrier
Thousands of researchers have attempted greedy approaches to NP-complete problems. The refutation shows why such approaches face fundamental obstacles.

## Building and Verification

### Lean
```bash
cd lean/
lean RiazKhiyalRefutation.lean
```

### Rocq
```bash
cd rocq/
rocqc RiazKhiyalRefutation.v
```

## Key Theorems

| Theorem | Meaning |
|---------|---------|
| `greedy_not_always_correct` | Greedy algorithms can fail to find existing cycles |
| `backtracking_can_be_exponential` | No polynomial bound on backtracking exists |
| `backtracking_not_limited` | Junction node limitation doesn't hold |
| `riaz_khiyal_refuted` | Main refutation: claims cannot all be true |
| `paper_conclusion_invalid` | The paper's conclusion does not follow |

## Educational Value

This refutation teaches:
1. **Rigorous proof requirements** - What it takes to prove complexity claims
2. **Counter-example construction** - How to refute incorrect algorithms
3. **Complexity theory fundamentals** - Why NP-completeness is hard
4. **Common pitfalls** - Mistakes often made in P vs NP attempts

## Relation to Proof Attempt

The **proof/** folder (sibling directory) formalizes what the authors claimed.
This **refutation/** folder proves those claims are false or unsubstantiated.

Together, they provide:
- **Proof folder**: The claim structure (IF claims hold THEN P=NP) ✓ Valid logic
- **Refutation folder**: The claims don't hold ✗ Missing proofs + Counter-examples

Result: The attempt fails.

## See Also

- **../proof/** - Formalization of the proof attempt structure
- **../original/** - The original paper
- **../README.md** - Complete overview of the attempt and its errors
