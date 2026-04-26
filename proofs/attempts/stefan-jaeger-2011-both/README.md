# Stefan Jaeger (2011) - Both (P=NP and P≠NP)

**Attempt ID**: 72 (from Woeginger's list)
**Author**: Stefan Jaeger
**Year**: 2011 (April)
**Claim**: Both — P=NP (with the first Peano axiom) and P≠NP (without the first Peano axiom)
**Status**: Refuted

## Summary

In April 2011, Stefan Jaeger submitted a paper titled "Computational Complexity on Signed Numbers" to arXiv (arXiv:1104.2538). The paper introduces a novel representation of natural numbers called "b-numbers" that includes a sign bit indicating uncertainty about the existence of the number zero. Jaeger argues that the first Peano axiom (which asserts the existence of the number zero) is not essential for defining natural numbers.

Using this alternative representation, Jaeger claims to prove two complementary results:
- **With the first Peano axiom**: P = NP
- **Without the first Peano axiom**: P ⊊ NP (P is a proper subset of NP)

The paper is notable for the "Both" claim — it asserts that the answer to the P vs NP question depends on which foundational axioms one accepts. This is the key reason it appears as entry #72 on Woeginger's list of P vs NP proofs.

## Core Idea

### B-Numbers: A Novel Representation

Jaeger proposes "b-numbers" (binary numbers with a sign bit) as an alternative to the standard natural number representation. A b-number `b = b_n b_{n-1} ... b_1 | b_0` consists of:
- **Actual encoding bits** (`b_n ... b_1`): A binary encoding of a natural number
- **Sign bit** (`b_0`): Indicates whether zero is encoded as `0` (sign=1) or as `1` (sign=0)

The key insight Jaeger claims: without the first Peano axiom, we cannot be certain which encoding convention is correct, introducing "intrinsic uncertainty" into every computation.

### Intrinsic Uncertainty

The sign bit creates two possible encodings for every b-number, and without the first Peano axiom, we cannot know which is correct. Jaeger defines:
- **Entropy theorem** (Theorem 1): The uncertainty `E(b)` of a b-number `b` satisfies `I(1/(b+1)) ≤ E(b) ≤ I(1/(⌈log₂(b+1)⌉+1))`
- **Entropy reduction theorem** (Theorem 2): For any computation `C` and any `ε > 0`, there exists an equivalent computation `C'` with uncertainty `E(C') < ε` by adding bits to the input

### The Complexity Claims

- **Theorem 3 (P theorem)**: With the first Peano axiom, P=NP. The argument is that the axiom fixes the sign bit, forcing computations to use either exponential or polynomial encoding. Assuming the input bits are correct leads to a polynomial runtime.
- **Theorem 4 (PNP theorem)**: Without the first Peano axiom, P≠NP. A machine that checks with uncertainty `I(1/(2b+1))` whether T' accepts input b requires exponential time by a diagonal argument.

## The Error

### Fundamental Flaw: Redefining Complexity Classes Doesn't Resolve P vs NP

The primary error is that Jaeger's "proof" operates in a non-standard model that fundamentally changes the definitions of P and NP. The standard P vs NP question concerns deterministic and non-deterministic Turing machines accepting languages over fixed alphabets, with the runtime measured by the number of steps — not by any notion of uncertainty about number representations.

### Specific Errors

**1. Equivocation on "computation" and "complexity":**
The standard definitions of P and NP count computation steps on a Turing machine. Jaeger redefines complexity in terms of "uncertainty reduction" through bit padding. These are not the same notion of complexity, and results proved about one do not transfer to the other.

**2. The "proof" of P=NP (Theorem 3) is circular:**
Jaeger argues that by assuming the first Peano axiom, "no actual computation is needed for T to solve the problem." In other words, the machine can output any bit after padding the input sufficiently. But this means T does not actually solve the decision problem — it merely terminates after polynomial time without verifying membership. This is not a valid algorithm for NP problems.

**3. Padding with bits is not the same as solving a decision problem:**
The entropy reduction theorem (Theorem 2) says that uncertainty can be reduced by adding bits to the input and applying a bijective mapping. But adding bits to an input changes the input itself — the mapping M changes the computational problem. The "equivalent computation" is not solving the same problem on the same input.

**4. The diagonal argument in Theorem 4 is flawed:**
Theorem 4 claims that the machine T (which checks whether T' accepts b) requires exponential time for the special case T'=T, b=T. However, this self-referential argument does not properly establish that the machine is in NP but not P. The argument relies on properties of the b-number encoding rather than the complexity of the underlying decision problem.

**5. Changing the number system does not change P vs NP:**
P vs NP is a question about computational problems, not about the representation of numbers. Any reasonable encoding of natural numbers (binary, unary, b-numbers) gives the same complexity classes, as long as encodings are polynomial-time convertible between each other. Jaeger's b-numbers, if properly defined, would not fundamentally change P or NP.

**6. The framework is not logically coherent:**
The paper asserts both P=NP and P≠NP in different "axiom systems," but both conclusions follow from informal and imprecise arguments about uncertainty in bit representations. The distinction between the two cases is not crisply defined mathematically.

### Why This Approach Cannot Work

The P vs NP problem is well-defined in any standard model of computation. Results like the time hierarchy theorem show that there exist problems requiring more time as resources increase. Changing the axioms of arithmetic or the representation of numbers cannot resolve P vs NP because:

1. The question is about the existence of efficient algorithms for specific problems (SAT, graph coloring, TSP, etc.)
2. These problems are defined independently of number representations
3. Polynomial-time equivalence of standard encodings means representation changes do not affect complexity classes
4. The first Peano axiom is accepted in all standard mathematical frameworks; excluding it creates a non-standard model that does not correspond to the actual P vs NP problem

## Broader Context

### Axiomatic Approaches to P vs NP

Some legitimate research has explored whether P vs NP is independent of ZFC set theory or other axiomatic systems. However, such research uses precise logical frameworks (forcing, oracles, natural proofs barriers) and does not claim to prove P=NP or P≠NP outright — it would only show the question is undecidable in a particular system.

Jaeger's approach is different: he modifies the mathematical foundations (by removing a Peano axiom) and claims this changes the answer. This conflates:
- Logical independence (cannot prove OR disprove from axioms)
- Conditional provability (can prove from axioms X but not axioms Y)

### Related Work

Jaeger references an earlier paper (arXiv:0811.0463, 2008) where he explored similar ideas about "intrinsic uncertainty" and P/NP. The 2011 paper is an extension of that earlier work.

## Why the Claim is Tempting

The approach has surface appeal because:
- It invokes real mathematical concepts (Peano axioms, entropy, information theory)
- The "Both" claim seems sophisticated and nuanced
- Information theory and coding theory are genuinely relevant to complexity theory
- The idea that P vs NP might depend on foundations has some philosophical resonance

However, the argument fails because it conflates foundational questions about number existence with algorithmic complexity questions about problem-solving efficiency.

## Key Lessons

1. **Changing representations does not change complexity**: Standard complexity classes are robust to polynomial-time-equivalent encodings.
2. **Uncertainty in representation ≠ computational complexity**: Information-theoretic uncertainty is not the same as worst-case computational complexity.
3. **Removing axioms creates non-standard models**: Abandoning the first Peano axiom gives a non-standard system, not the standard natural numbers that P vs NP is about.
4. **Both P=NP and P≠NP cannot be true**: In any consistent formal system that includes the standard natural numbers, either P=NP or P≠NP (not both), so a "proof" of both is necessarily flawed.
5. **Self-referential arguments require care**: Diagonal arguments must be precise; an informal "by a diagonal argument" does not constitute a proof.

## Formalization Goals

This directory formalizes:

1. **The b-number representation**: Definitions of b-numbers and the sign bit
2. **The entropy claims**: Theorem 1 (Entropy theorem) formalized
3. **The flawed P=NP claim**: Jaeger's Theorem 3 formalized, showing where the argument breaks down
4. **The flawed P≠NP claim**: Jaeger's Theorem 4 formalized, showing the diagonal argument's gap
5. **The refutation**: Why standard complexity theory is invariant under encoding changes

## References

### Primary Source

- **Original Paper**: Jaeger, S. (2011). "Computational Complexity on Signed Numbers"
  - arXiv:1104.2538v1 [cs.CC]
  - Submitted: April 13, 2011
  - Available at: https://arxiv.org/abs/1104.2538

### Related Work by Jaeger

- Jaeger, S. (2008). "Solving the P/NP Problem under Intrinsic Uncertainty"
  - arXiv:0811.0463v2
  - Available at: https://arxiv.org/abs/0811.0463

### Context

- **Woeginger's List**: Entry #72
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Related Issue**: #44 (General framework for P vs NP attempts)
- **Issue**: #473

## See Also

- [Repository README](../../../README.md) - Overview of the P vs NP problem
- [ATTEMPTS.md](../ATTEMPTS.md) - List of all formalized attempts
