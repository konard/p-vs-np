# Jerrald Meek (2008) - Refutation

## Why the Proof Fails

Meek's 2008 P≠NP attempt contains a fundamental error: **confusion between problem instances and problem classes**, plus a complete misunderstanding of what NP-Completeness means.

## The Fatal Error: Instance/Problem Confusion

### The Claim

Meek claimed that:
1. Base conversion (decimal to binary with powers of 2) is an NP-Complete problem
2. It can be solved in polynomial time
3. But this polynomial solution doesn't transfer to K-SAT
4. Therefore, P ≠ NP

### The Problem

**NP-Completeness** applies to **problem classes**, not **specific instance types**:

| Aspect | Meek's Understanding | Reality |
|--------|---------------------|---------|
| **What is NP-Complete?** | Specific instance types like base conversion | Entire problem classes (all instances) |
| **Special instances** | Form separate NP-Complete problems | Are just easy instances within hard problems |
| **Polynomial for some instances** | Contradicts NP-Completeness | Expected and common |
| **What would prove P=NP?** | Solving one instance type | Algorithm for ALL instances of an NP-Complete problem |

### Why This Is Fatal

1. **Conceptual Misunderstanding**: Base conversion is NOT an NP-Complete problem—it's a polynomial-time solvable special case of Knapsack
2. **Wrong Reduction Direction**: Meek shows SAT→BaseConversion, but NP-Hardness requires showing BaseConversion→SAT
3. **Invented "Postulate"**: Karp never claimed solving one NP-Complete problem instance should solve others
4. **Circular Reasoning**: Prior "theorems" assume P ≠ NP to prove P ≠ NP

## The Eight Fundamental Errors

### 1. Problem vs. Instance Confusion

**Meek thinks**:
- "Base conversion" is an NP-Complete PROBLEM
- Having a polynomial algorithm for it is surprising
- This creates a contradiction

**Reality**:
- "Base conversion" is a SPECIAL INSTANCE TYPE of Knapsack
- Having polynomial algorithms for special instances is normal
- SAT with 0 clauses is polynomial, but that doesn't make it "an NP-Complete problem"

### 2. Wrong Reduction Direction

To prove NP-Completeness, you need:
- **Reduction FROM your problem TO a known NP-Complete problem** (shows hardness)

Meek shows:
- **Reduction FROM K-SAT TO base conversion** (backwards!)

This is like saying: "SAT reduces to sorting, therefore sorting is NP-Complete"—completely wrong!

### 3. Misinterpretation of Karp's Theorem

**What Karp actually proved**:
- If ANY NP-Complete problem L has a polynomial algorithm for **all instances**, then P = NP

**What Meek thinks Karp proved**:
- Solving "one NP-Complete problem" should give you all others (invented "second postulate")

**Reality**:
- Algorithms must work on **all instances** of a problem class
- Special-case algorithms don't count

### 4. Circular Reasoning

Meek's "theorems" from prior papers essentially state:
- "P = NP Optimization Theorem": NP problems require examining > polynomial inputs
- "P = NP Partition Theorem": Can't partition efficiently

**The problem**: These "theorems" ASSUME P ≠ NP to prove P ≠ NP!

### 5. Incomplete Algorithmic Categorization

**Meek claims**: All algorithms fall into 4 categories, all ruled out

**Reality**: The categorization is informal and incomplete:
- Algebraic algorithms
- Geometric algorithms
- Randomized algorithms with derandomization
- Novel computational models
- Many other sophisticated approaches

### 6. Special Cases Tell Us Nothing

**Throughout the paper**: Meek shows some special instances are hard

**Missing**: Proof that **ALL instances** require super-polynomial time

Showing that some approaches don't work ≠ showing NO approach can work

### 7. Misunderstanding Karp Reductions

**Meek argues** (Section 4.3): Optimized Knapsack uses "quality Q" of S, but other NP problems don't provide S, so the algorithm gives "undefined"

**Wrong because**: Karp reductions CONSTRUCT S from the SAT instance—the reduction provides the transformation!

### 8. Unproven Dependencies

All of Meek's "theorems" from prior papers are:
- Not established results in complexity theory
- Not peer-reviewed or validated
- Appear to contain similar errors
- Used as foundation for this "proof"

## Concrete Example of the Error

**Meek's Logic**:
```
1. SAT with formula (x OR y) reduces to finding binary digits of 3
2. Binary conversion is polynomial-time solvable
3. Therefore "binary conversion" is an NP-Complete problem
4. But solving it doesn't solve general SAT
5. Therefore P ≠ NP
```

**Why It's Wrong**:
```
1. "Binary conversion" is just ONE INSTANCE TYPE, not a problem class
2. It's like saying "SAT with 0 clauses is NP-Complete"
3. The fact that SOME instances are easy tells us NOTHING
4. To prove P=NP, you need an algorithm for ALL instances
5. Meek's argument is based on a category error
```

## What Would Be Needed for a Valid Proof

A valid P ≠ NP proof must:

1. ✅ **Work for all instances**: Prove super-polynomial bound for ALL inputs
2. ✅ **Understand definitions**: Know the difference between instances and problems
3. ✅ **Avoid circularity**: Don't assume what you're trying to prove
4. ✅ **Address barriers**: Deal with relativization, natural proofs, or algebraization
5. ✅ **Use formal methods**: Work within computational complexity theory framework

Meek's attempt:
1. ❌ Only considers special cases
2. ❌ Fundamentally misunderstands NP-Completeness
3. ❌ Uses circular reasoning
4. ❌ Doesn't address any barriers
5. ❌ Uses informal arguments

## The Subproblem Structure

### What Meek Needs to Prove

For P ≠ NP, must show: **Every NP-Complete problem has instances requiring super-polynomial time**

### What Meek Actually Shows

"Some special instances can be solved in polynomial time, but the algorithm doesn't generalize"

**Gap**: Easy instances ≠ proof of general hardness

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`instance_vs_problem_distinction`**: Problems are sets of instances; special cases ≠ problem classes
2. **`base_conversion_not_npc`**: Base conversion is not NP-Complete (wrong reduction direction)
3. **`meek_fatal_error`**: Special-case algorithms don't determine general problem complexity
4. **`circular_dependency_in_theorems`**: Prior "theorems" assume P ≠ NP
5. **`incomplete_categorization`**: The four algorithm categories don't exhaust all possibilities

## Key Lessons

1. **Precision Matters**: Understanding formal definitions is essential
2. **Instances ≠ Problems**: Special cases within hard problems can be easy
3. **Direction Matters**: Reductions must go the right way for NP-Hardness
4. **No Circular Logic**: Can't assume what you're proving
5. **Informal ≠ Proof**: Categorizations must be mathematically rigorous

## The Peer Review Outcome

This attempt:
- Was never published in a peer-reviewed venue
- Received critical feedback (acknowledged in the paper)
- Timothy Chow pointed out the instance/problem confusion
- Lance Fortnow warned about the difficulty of the problem
- Remains on arXiv as version 5 (September 2008)

## References

- **Meek, J.** (2008). "Analysis of the postulates produced by Karp's Theorem", arXiv:0808.3222
- **Karp, R. M.** (1972). "Reducibility Among Combinatorial Problems"
- **Garey, M. R., Johnson, D. S.** (1979). "Computers and Intractability"
- **Woeginger's List**: Entry #46 - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
