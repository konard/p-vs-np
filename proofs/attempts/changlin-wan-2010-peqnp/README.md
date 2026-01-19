# Changlin Wan (2010) - P=NP Attempt

**Attempt ID**: 61 (from Woeginger's list)
**Author**: Changlin Wan (with Zhongzhi Shi)
**Year**: May 2010
**Claim**: P=NP
**Paper**: [arXiv:1005.3010](http://arxiv.org/abs/1005.3010) - "A Proof for P =? NP Problem"
**Status**: **WITHDRAWN** by author (July 1, 2020) - Contains fundamental errors

---

## Summary

In May 2010, Changlin Wan and Zhongzhi Shi published a paper claiming to prove P=NP through a theoretical framework centered on recursive definitions of Turing machines. The paper attempted to show that all decidable languages can be unified in a way that collapses P and NP. The author later withdrew the paper and acknowledged it contained "wild thoughts and immature article writing."

## Main Argument/Approach

### Core Strategy

The paper's approach involves several abstract steps:

1. **Recursive Definition of Turing Machines**: Creating "a recursive definition for Turing machine that accepts the encoding strings of valid TMs"

2. **Infinite Sequence Construction**: Constructing "an infinite sequence of TM" claimed to encompass all valid Turing machines

3. **Decidable Language Class D**: Defining class **D** containing all decidable languages, with union and reduction operators

4. **Union Language Up**: Building a language called **Up** representing the union of all languages in **D**

5. **Main Claim**: Concluding that P = Up and Up = NP, therefore P = NP

### Paper Structure

The paper attempts to prove the equality by showing:
- P ⊆ Up (all polynomial-time languages are in the union)
- Up ⊆ NP (the union is contained in NP)
- Up ⊆ P (the union is polynomial-time decidable)

If all three were true, this would imply P = NP.

## The Errors in the Proof

### Location of Errors

The paper contains multiple fundamental errors throughout, but the most critical issues are:

1. **Ill-defined recursive construction** (Section on TM enumeration)
2. **Confusion about computability vs complexity** (Throughout)
3. **Invalid union construction** (Definition of Up)
4. **Circular reasoning** (Proof that Up ⊆ P)

### Detailed Error Analysis

#### Error 1: Recursive TM Definition Problems

**The Claim**: The paper claims to create a recursive definition that captures all valid Turing machines.

**The Problem**:
- The set of all Turing machines is already well-defined and enumerable (this is standard computability theory)
- Creating a "recursive definition" doesn't add anything new or solve the P vs NP problem
- The paper conflates the enumeration of TMs with the classification of their complexity

**Why This Matters**: Even if we can enumerate all TMs (which we can), this doesn't tell us anything about the relationship between P and NP. The difficulty is in **determining which TMs run in polynomial time**, not in enumerating TMs themselves.

#### Error 2: Confusion Between Decidability and Complexity

**The Problem**: The paper defines class **D** as containing all decidable languages. But:
- **Decidable** = can be decided by some TM (no time bound)
- **P** = can be decided in polynomial time
- **NP** = can be verified in polynomial time

These are fundamentally different concepts:
- D contains undecidable problems (halting problem, etc.) - **WRONG**, D should only contain decidable
- D is strictly larger than both P and NP
- D = RE ∩ co-RE (recursively enumerable and co-recursively enumerable)

**The Confusion**: The paper treats decidability (computability) as if it's the same as polynomial-time decidability (complexity).

#### Error 3: Invalid Construction of Up

**The Claim**: The language Up is defined as the union of all languages in D.

**The Problems**:
1. **Union is not well-defined**: The union of all decidable languages is not itself a language in the usual sense
2. **Not a formal language**: A formal language is a subset of Σ*, but "union of all decidable languages" is a meta-level construction
3. **Cardinality issues**: The set of all decidable languages is uncountable (contains all subsets of N), making the union ill-defined

**What Would Be Needed**: A precise mathematical definition of how this union is constructed and what membership in Up means.

#### Error 4: Circular Reasoning in Up ⊆ P

**The Claim**: The paper claims to show that Up (the union of all decidable languages) is in P.

**The Circularity**:
- To show Up ∈ P, we'd need a polynomial-time algorithm for Up
- But Up is defined to contain all decidable languages
- If Up ∈ P, then every decidable language would be in P
- This would mean EXPTIME = P, 2-EXPTIME = P, etc. (absurd!)

**The Error**: The proof assumes what it needs to prove. It doesn't actually construct a polynomial-time algorithm for deciding membership in Up.

#### Error 5: Misunderstanding of NP

**The Problem**: The paper seems to confuse:
- **NP** (nondeterministic polynomial time)
- **Class of all NP problems**
- **Union of all languages in NP**

**Why This Matters**:
- NP is already a well-defined complexity class
- Showing "Up = NP" doesn't make sense unless Up is also a complexity class
- The paper doesn't establish that Up has any particular complexity property

### Fundamental Conceptual Issues

#### 1. Mixing Levels of Abstraction

The paper mixes:
- **Object level**: Individual languages and TMs
- **Meta level**: Classes of languages and TMs
- **Complexity**: Time bounds on computation

These must be kept separate in rigorous proofs.

#### 2. Lack of Formal Definitions

Critical terms are undefined:
- What exactly is the "recursive definition" of TMs?
- How is membership in Up decided?
- What is the claimed polynomial-time algorithm?

#### 3. No Concrete Algorithm

Unlike valid attempts that provide explicit algorithms (even if flawed), this paper:
- Provides no concrete algorithm for any NP-complete problem
- Gives no complexity analysis
- Offers no pseudocode or implementation

### Why the Author Withdrew the Paper

The author's own comment on arXiv: "sorry for the wild thoughts and immature article writting" [sic]

This suggests the author recognized:
- The ideas were not fully developed
- The mathematical rigor was insufficient
- The fundamental approach was flawed

## Known Refutations

### General Refutation

While no formal published refutation exists (the paper was withdrawn before peer review), the errors are clear to anyone with training in:

1. **Computability Theory**: The confusion between decidability and complexity is a fundamental error
2. **Complexity Theory**: The construction of Up violates basic principles of formal language theory
3. **Logic**: The circular reasoning in the main proof is invalid

### Standard Barriers Not Addressed

The paper does not address known barriers to proving P vs NP:
- **Relativization** (Baker-Gill-Solovay, 1975): The proof would relativize, but there exist oracles where P^A ≠ NP^A
- **Natural Proofs** (Razborov-Rudich, 1997): Any proof based on properties of languages must avoid being "natural"
- **Algebrization** (Aaronson-Wigderson, 2008): Modern barrier for algebraic techniques

The abstract approach in the paper would fall victim to relativization, as it doesn't use any non-relativizing properties.

## Formalization Strategy

Our formalization demonstrates the errors by:

1. **Defining complexity classes formally**: P, NP, EXPTIME, and decidable languages
2. **Formalizing the paper's claims**: What "Up" would mean if it could be defined
3. **Identifying the gaps**: Showing that the claimed construction doesn't work
4. **Proving impossibility**: Demonstrating that Up ⊆ P would imply absurd consequences (like EXPTIME = P)

## Implementation Structure

- **`coq/WanAttempt.v`**: Coq formalization
- **`lean/WanAttempt.lean`**: Lean 4 formalization
- **`isabelle/WanAttempt.thy`**: Isabelle/HOL formalization

Each formalization:
1. Defines complexity classes (P, NP, EXPTIME)
2. Defines the concept of decidable languages
3. Attempts to formalize "Up" and shows the construction fails
4. Shows that if Up existed and was in P, it would collapse the complexity hierarchy
5. Concludes that the paper's approach is fundamentally flawed

## Key Lessons

### What the Paper Got Wrong

1. ✗ Confused decidability with polynomial-time decidability
2. ✗ Attempted to construct ill-defined union of all decidable languages
3. ✗ Provided no concrete algorithm or complexity analysis
4. ✗ Used circular reasoning in the main proof
5. ✗ Mixed meta-level and object-level reasoning
6. ✗ Did not address known barriers to proving P vs NP

### Common Pitfalls Illustrated

1. **Computability ≠ Complexity**: Just because something is computable doesn't mean it's efficiently computable
2. **Enumeration ≠ Decision**: Enumerating all TMs doesn't help decide which are polynomial-time
3. **Meta-level constructions**: Care must be taken when reasoning about "all languages" or "all TMs"
4. **Need for concrete algorithms**: P vs NP is about concrete computational complexity, not abstract existence

### Educational Value

This attempt illustrates:
- The importance of precise definitions in complexity theory
- Why computability and complexity are different fields
- The danger of mixing abstraction levels
- Why P vs NP requires concrete algorithmic insights, not just abstract reasoning

### Barriers Not Addressed

The paper does not address:
- **Relativization** (Baker-Gill-Solovay, 1975)
- **Natural Proofs** (Razborov-Rudich, 1997)
- **Algebrization** (Aaronson-Wigderson, 2008)

Any valid proof of P = NP or P ≠ NP must overcome at least one of these barriers.

## References

### The Original Paper

- Wan, C., & Shi, Z. (2010). "A Proof for P =? NP Problem." arXiv:1005.3010 [cs.CC] **[WITHDRAWN]**
  - URL: https://arxiv.org/abs/1005.3010
  - Withdrawn: July 1, 2020
  - Author's comment: "sorry for the wild thoughts and immature article writting"

### Background on P vs NP

- Cook, S. A. (1971). "The complexity of theorem proving procedures." *Proceedings of the 3rd ACM Symposium on Theory of Computing*, 151-158.
- Karp, R. M. (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, 85-104.
- Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.* W. H. Freeman.

### Relevant Theory

- **Computability Theory**:
  - Turing, A. M. (1936). "On computable numbers, with an application to the Entscheidungsproblem."
  - Sipser, M. (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.

- **Complexity Theory**:
  - Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach.* Cambridge University Press.

- **Barriers to P vs NP**:
  - Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP Question." *SIAM Journal on Computing*, 4(4), 431-442.
  - Razborov, A. A., & Rudich, S. (1997). "Natural Proofs." *Journal of Computer and System Sciences*, 55(1), 24-35.
  - Aaronson, S., & Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory." *ACM Transactions on Computation Theory*, 1(1), 1-54.

## Woeginger's List

This attempt appears as **Entry #61** in Gerhard Woeginger's famous list of P vs NP attempts:
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Verification Status

- ✅ Coq formalization: Identifies the fundamental errors
- ✅ Lean formalization: Shows the construction is ill-defined
- ✅ Isabelle formalization: Proves that the claimed properties lead to contradictions

## License

This formalization is provided for educational and research purposes under the repository's main license (The Unlicense).

---

**Navigation**: [↑ Back to Proofs](../../) | [Repository Root](../../../README.md) | [Issue #463](https://github.com/konard/p-vs-np/issues/463)
