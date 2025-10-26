# Sanchez Guinea (2015) - P=NP Attempt

**Attempt ID**: 103
**Author**: Alejandro Sánchez Guinea
**Year**: 2015
**Claim**: P=NP (via polynomial-time 3-SAT algorithm)
**Paper**: "Understanding SAT is in P" (arXiv:1504.00337v4)
**Source**: [Woeginger's P vs NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) - Entry #103

## Summary

In April 2015, Alejandro Sánchez Guinea claimed to prove P=NP by designing an algorithm that solves 3-SAT in polynomial time. The paper introduces the concept of an "understanding" - a three-valued function mapping literals to {true, false, free} - and uses "contexts" and "concepts" to construct satisfying assignments without searching the solution space. The author claims the main algorithm (Algorithm U) runs in O(m²) time, where m is the number of clauses.

## Main Argument

### Core Idea

Instead of traditional truth assignments α: X → {0,1}, the paper uses an **understanding** ũ: L → {t, f, ε} where:
- t = true
- f = false
- ε = free (unassigned)

### Key Definitions

1. **Context**: For a 3-SAT clause φ = {l₁, l₂, l₃}, the context of literal l₁ is the set {l₂, l₃}

2. **Concept**: A context interpreted under an understanding. For literal l₁ in φ, its concept is C: {ũ(l₂), ũ(l₃)}

3. **Concept Types**:
   - **Type C⁺**: Both literals false, OR both free, OR one free and one false
   - **Type C***: Both literals true, OR one true and one false, OR one free and one true

4. **Understanding of a Literal**: For literal λ in clause set φ:
   - ũ(λ) = ε if C̃[λ] is empty or (C̃[λ]⁻ is empty and C̃[λ] is type C̃*)
   - ũ(λ) = t if C̃[λ] is type C̃⁺ and C̃[λ]⁻ is empty
   - ũ(λ) = f if C̃[λ]⁻ is not empty and C̃[λ] is not type C̃⁺
   - undefined otherwise

Where:
- C̃[λ] = set of all concepts of λ
- C̃[λ]⁻ = set of concepts of type C⁺ in C̃[¬λ]

### The Algorithm

**Algorithm U** (Main algorithm):
1. Start with empty understanding ũ and empty clause set φ
2. For each clause ϕ in Φ:
   - If all literals in ϕ are false under ũ, use Algorithm D to free at least one
   - Add concepts from ϕ to the concept set
   - Update understanding via ⟨Compute ũ⟩
3. If successful for all clauses, output ũ (which corresponds to a satisfying assignment)
4. Otherwise, Φ is unsatisfiable

**Algorithm D** (Make a false literal free):
- Given a literal λ that is false under ũ
- Try each concept C in C̃[λ]⁻
- For each literal l in C:
  - If l is false, recursively call Algorithm D to free it (with updated set H to avoid circular dependencies)
  - Check if l can be made true using Algorithm G
  - If both conditions succeed, set l to true and propagate changes
- If successful for any concept, λ becomes free

**Algorithm G** (Check if literal can be true):
- Given a free literal λ
- Try each concept C in C̃'[λ]
- Assume λ is true, set both literals in C to "not true"
- Run ⟨Compute ũ'⟩ to check for contradictions
- If no contradiction for any concept, λ can be made true

**⟨Compute ũ⟩ Operation**:
- Recompute ũ for each literal whose concept type changed
- Iterate until no more changes occur (fixed-point)

### Claimed Results

**Theorem 1 (Correctness)**: Algorithm U terminates successfully if and only if Φ is satisfiable

**Theorem 2 (Polynomial Time)**: Algorithm U terminates in O(m²) time where m = number of clauses

## The Error

The error lies in the **time complexity analysis** (Section 2.2). The paper claims O(m²) complexity, but the analysis is fundamentally flawed:

### Critical Issues

#### 1. **Recursive Depth Not Properly Bounded**

Algorithm D calls itself recursively (step D4):
```
D4. If l is false under ũ', then ... define an understanding ũ''
    equivalent to ũ' such that l is free under ũ'' (this is done
    by Algorithm D)
```

The paper claims:
> "the maximum number of iterations of Algorithm D overall (including its recursive call in D4 for some literals in concepts in C̃[λ]⁻) is bounded by the total number of clauses in φ"

This is **unsubstantiated**. The recursion:
- Can nest arbitrarily deep through chains of dependent literals
- The set H grows to track dependencies but doesn't bound recursion depth
- Each level could branch to multiple recursive calls
- No formal proof limits the recursion depth to O(m)

#### 2. **⟨Compute ũ⟩ Complexity Ignored**

The fixed-point computation ⟨Compute ũ⟩:
- Is called at multiple points in each algorithm
- Must iterate "until there is no change of type on any subset of concepts"
- Could propagate changes through the entire concept graph
- Each iteration examines all concepts (up to 3m concepts)
- Number of iterations to reach fixed-point is unbounded in the analysis

The paper hand-waves this with:
> "In the worst case this process goes through all concepts that have been defined with respect to φ. That is, at most three times the number of clauses in φ."

But this only bounds **one iteration**, not the number of iterations to converge.

#### 3. **Informal "Arithmetic Series" Argument**

The proof of Theorem 2 states:
> "we get roughly an arithmetic series as the number of operations performed"
> "we have an upper bound of approximately O(m²)"

Words like "roughly" and "approximately" are **not acceptable in complexity proofs**. The analysis:
- Doesn't provide exact recurrence relations
- Doesn't account for all nested loops
- Doesn't properly bound recursive calls
- Uses informal reasoning instead of rigorous analysis

#### 4. **Hidden Exponential Blowup**

The actual complexity appears to be **exponential** because:
- Algorithm D recursively calls itself on literals in concepts
- Each recursive call can branch to multiple sub-calls
- The recursion depth could reach O(m) in the worst case
- At each level, we might try multiple concepts
- Total calls: potentially O(c^m) for some constant c

### Why This Matters

If the algorithm actually runs in exponential time, then:
- **P ≠ NP claim fails**: The algorithm doesn't solve 3-SAT in polynomial time
- The approach might still be correct (finds satisfying assignments when they exist)
- But it's just another exponential-time SAT solver, not a breakthrough

### Formal Verification Reveals the Error

When we attempt to formalize Theorem 2 (polynomial time complexity), we must:
1. Define a **cost model** that counts all operations
2. Prove **termination bounds** for recursive Algorithm D
3. Prove **convergence bounds** for ⟨Compute ũ⟩
4. Provide **explicit recurrence relations**

The formalization will fail because:
- We cannot prove Algorithm D's recursion depth is O(m)
- We cannot prove ⟨Compute ũ⟩ converges in polynomial iterations
- The recurrence relation for total time is exponential

## Formalizations

We provide three formal verification attempts that expose the complexity analysis error:

- **[Coq](coq/)**: Formalizes algorithms and attempts to prove polynomial time bound
- **[Lean](lean/)**: Formalizes algorithms and complexity, shows bound cannot be proven
- **[Isabelle](isabelle/)**: Formalizes algorithms and provides counterexample to O(m²) claim

Each formalization demonstrates that the polynomial time claim cannot be established with the given arguments.

## References

- **Original Paper**: Alejandro Sánchez Guinea, "Understanding SAT is in P", arXiv:1504.00337v4 [cs.CC], September 2016
- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #103)
- **Related Work**: Davis-Putnam-Logemann-Loveland (DPLL) algorithm, Conflict-Driven Clause Learning (CDCL)

## Credits

Analysis and formalization by the P vs NP formal verification project.
