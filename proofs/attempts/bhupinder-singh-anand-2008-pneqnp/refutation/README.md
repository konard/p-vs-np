# Refutation of Anand 2008

This directory contains formal refutations of the Anand 2008 P ≠ NP proof attempt.

## Contents

- `lean/AnandRefutation.lean` - Lean 4 refutation
- `rocq/AnandRefutation.v` - Rocq refutation

## The Core Error: Category Confusion

Anand's attempt fundamentally confuses **computability theory** with **complexity theory**:

### Two Distinct Hierarchies

**Computability Theory** (Gödel, Turing):
- Question: Can a problem be solved **at all**?
- Categories: Decidable vs Undecidable
- Example: Halting problem is undecidable

**Complexity Theory** (Cook, Karp):
- Question: How **efficiently** can a decidable problem be solved?
- Categories: P, NP, EXPTIME, etc.
- Example: SAT is in NP, unknown if in P

### The Invalid Leap

Anand's argument:
1. Gödel showed some arithmetical relations are "constructively computable" but not "Turing-computable"
2. This is analogous to the P vs NP distinction
3. Therefore P ≠ NP

**Why this fails:**
- "Constructively computable" (Anand) = verifiable with arbitrary time
- "Turing-computable" (Anand) = decidable algorithmically
- **NP** = verifiable in **polynomial time**
- **P** = decidable in **polynomial time**

The time bounds (polynomial vs exponential) are **completely absent** from Anand's framework!

## Detailed Refutation Points

### 1. Misapplication of Gödel's Results

**Gödel's incompleteness theorems concern:**
- Formal provability in axiomatic systems
- Which statements can be proven from axioms
- Meta-mathematical properties of formal systems

**P vs NP concerns:**
- Time complexity of algorithms
- Polynomial vs exponential running time
- Computational resources required

**These are orthogonal questions!**

### 2. All P and NP Problems Are Decidable

By definition:
- Every problem in P is decidable (has an algorithm)
- Every problem in NP is decidable (has an algorithm)
- Undecidable problems are **outside** both P and NP

Therefore, Gödel's results about **undecidable** problems cannot inform the P vs NP question, which concerns **decidable** problems.

### 3. Missing Time Complexity Analysis

A valid proof of P ≠ NP must show:
- A specific problem in NP
- Requires **super-polynomial time** to solve
- Using complexity-theoretic techniques

Anand's paper provides:
- ❌ No analysis of polynomial vs exponential time
- ❌ No lower bounds on time complexity
- ❌ No discussion of computational resources
- ❌ No complexity-theoretic framework

### 4. The "Trivial" Admission

Anand himself admits the solution is:
- "Trivial"
- "Not significant computationally"

This reveals the argument doesn't address **computational** complexity, only **logical** distinctions.

### 5. Undefined Terms

"Constructive computability" in Anand's framework:
- Allows **arbitrary time** for verification
- Not equivalent to NP's **polynomial-time** verification
- Missing: any time complexity bounds

### 6. The Correct Relationship

```
Computability Theory          Complexity Theory
(Can we solve it?)           (How efficiently?)
├─ Decidable ──────────┐
│  └─ All P, NP        ├─── P (poly-time decidable)
│                      ├─── NP (poly-time verifiable)
│                      └─── EXPTIME, etc.
└─ Undecidable
   ├─ Halting
   ├─ Gödel sentences
   └─ ...
```

Anand attempts to use results from the "Undecidable" branch to prove things about the P vs NP distinction within the "Decidable" branch. This is a **category error**.

## Formalization Strategy

The refutation formalizations:

1. Define both computability and complexity hierarchies
2. Show they are distinct
3. Demonstrate that all P and NP problems are decidable
4. Show that Gödel's undecidability results don't apply to P vs NP
5. Identify where the invalid inferential leap occurs
6. Use `sorry`/`Admitted` to mark the gap that cannot be bridged

## Conclusion

Anand's attempt fails because it:
- Confuses computability (solvability) with complexity (efficiency)
- Misapplies results from formal logic to computational complexity
- Provides no analysis of time complexity
- Makes an invalid analogical leap
- Admits to lacking computational significance

A valid proof of P ≠ NP must work within complexity theory and prove lower bounds on time complexity, not invoke results from computability theory.

## See Also

- [`../proof/README.md`](../proof/README.md) - The attempted proof
- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Original paper content
