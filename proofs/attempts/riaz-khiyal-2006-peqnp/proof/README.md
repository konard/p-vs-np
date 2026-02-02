# Proof Attempt Formalization

This folder contains formal translations of the Riaz-Khiyal proof attempt into proof assistant languages. These formalizations follow the structure of the original paper's argument, demonstrating what the authors claimed to prove and where the proof has gaps.

## Purpose

The formalization serves to:
1. **Clarify the argument structure** - Make explicit what was claimed in the paper
2. **Identify proof gaps** - Show precisely where proofs are missing or incomplete
3. **Demonstrate logical dependencies** - Show what would follow IF the claims were proven
4. **Enable verification** - Allow automated checking of the formalized statements

## Structure

Each formalization follows this pattern:

1. **Basic definitions** - Complexity classes (P, NP), graph theory, Hamiltonian cycles
2. **Algorithm structure** - The Riaz-Khiyal greedy algorithm with backtracking
3. **Key claims** - The unproven assertions (correctness, polynomial complexity, limited backtracking)
4. **Implications** - What would follow if the claims held (HC ∈ P → P = NP)
5. **Gaps** - Explicit markers showing where proofs are missing (`sorry` in Lean, `Admitted` in Rocq)

## Files

### Lean 4
- **lean/RiazKhiyalProof.lean** - Complete formalization in Lean 4
  - Uses standard library only (no Mathlib)
  - Compiles successfully with incomplete proofs marked
  - Demonstrates the logical structure of the argument

### Rocq (Coq)
- **rocq/RiazKhiyalProof.v** - Complete formalization in Rocq/Coq
  - Uses standard Coq libraries
  - Compiles successfully with `Admitted` for incomplete proofs
  - Parallel structure to the Lean formalization

## What These Formalizations Show

### The Argument Structure (Valid)

The formalization demonstrates that **IF** the following claims were proven:

1. **Correctness**: The algorithm finds a Hamiltonian cycle whenever one exists
2. **Polynomial Complexity**: The algorithm runs in polynomial time
3. **Limited Backtracking**: Backtracking occurs only at polynomially-many junction nodes

**THEN** the conclusion would follow: P = NP (since Hamiltonian Cycle is NP-complete)

This logical structure is sound. The problem is that the claims (1-3) are not proven in the paper.

### The Missing Proofs

The formalization explicitly marks where proofs are missing:

- **No proof of correctness** - The algorithm might miss some Hamiltonian cycles
- **No proof of polynomial complexity** - The worst-case running time is not analyzed
- **No proof about backtracking** - The claim about junction nodes is unsubstantiated
- **No engagement with counter-examples** - Known adversarial graph structures are not addressed

## Key Definitions

### Hamiltonian Cycle Problem
```lean
-- A Hamiltonian cycle visits every vertex exactly once and returns to start
structure HamiltonianCycle (g : Graph) where
  path : Path g
  coversAllNodes : path.length = g.numNodes
  allDistinct : ∀ i j, i < path.length → j < path.length → i ≠ j → path.nodes i ≠ path.nodes j
  returnToStart : g.hasEdge (path.nodes (path.length - 1)) (path.nodes 0) = true
```

### The Algorithm Structure
```lean
structure RKAlgorithm where
  preprocess : Graph → Bool
  selectNext : Graph → (Nat → Nat) → Nat → Nat
  shouldBacktrack : Graph → (Nat → Nat) → Nat → Bool
```

### The Critical Claims (Unproven)
```lean
-- CLAIM 1: Correctness
def HasCorrectness (alg : RKAlgorithm) : Prop :=
  ∀ g : Graph,
    (∃ hc : HamiltonianCycle g, True) →
    ∃ run : AlgorithmRun alg g, run.result.isSome

-- CLAIM 2: Polynomial Complexity
def HasPolynomialComplexity (alg : RKAlgorithm) : Prop :=
  ∃ T : TimeComplexity, isPolynomial T ∧
    ∀ g : Graph, ∀ run : AlgorithmRun alg g, run.steps ≤ T g.numNodes
```

## Building and Verification

### Lean
```bash
# Navigate to the lean folder
cd lean/

# Build with Lean 4
lake build

# Or verify directly
lean RiazKhiyalProof.lean
```

### Rocq
```bash
# Navigate to the rocq folder
cd rocq/

# Compile with Rocq
rocqc RiazKhiyalProof.v

# Or with Coq
coqc RiazKhiyalProof.v
```

## Relation to Refutation

This "proof" folder contains the **forward formalization** - what the authors claimed.

The **refutation/** folder (sibling directory) contains proofs that:
- The claims cannot all be satisfied
- Counter-examples exist
- The approach fundamentally cannot work

Together, these formalizations provide a complete picture: the proof attempt is well-structured logically, but lacks the necessary proofs and faces fundamental barriers.

## Notes

- All `sorry` (Lean) and `Admitted` (Rocq) statements represent gaps in the original paper
- The formalizations are intentionally incomplete to reflect the incompleteness of the original proof
- The goal is not to complete the proofs (which is impossible), but to clarify what is missing
- This is an educational formalization showing *why* the attempt fails, not a completed proof

## See Also

- **../refutation/** - Formal refutations showing why the claims cannot hold
- **../original/** - The original paper and its reconstruction
- **../README.md** - Overview of the entire attempt
