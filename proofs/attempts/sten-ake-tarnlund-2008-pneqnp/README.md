# Sten-Ake Tarnlund (2008) - P≠NP via First-Order Theory and Universal Turing Machines

**Attempt ID**: 48 (from Woeginger's list)
**Author**: Sten-Ake Tarnlund
**Year**: 2008 (revised 2009, updated through 2017)
**Claim**: P ≠ NP
**Status**: Refuted/Unaccepted

## Summary

In October 2008, Sten-Ake Tarnlund proposed a proof that P ≠ NP using a first-order logical theory of computing. The approach attempted to prove within a formal system that SAT (the Boolean satisfiability problem) cannot be solved in polynomial time, thereby establishing P ≠ NP. The proof was based on a single finite axiom characterizing a universal Turing machine and claimed to show that "SAT is not in P" is provable in a simply consistent extension of a first-order theory of computing.

## Main Argument

### The Approach

1. **First-Order Theory Foundation**: Tarnlund developed a first-order theory B of computing with axioms characterizing a universal Turing machine
2. **Formal Extension**: He created a simply consistent extension B' of this theory
3. **Provability Claim**: Within this formal system, he claimed to prove that "SAT is not in P"
4. **Meta-Theoretical Conclusion**: From this provability result, he argued that P ≠ NP follows as a mathematical truth

### Key Technical Claims

The crucial elements were:
- A **single finite axiom** sufficient to characterize universal Turing machines
- A **simply consistent extension** of the base theory that can prove computational complexity bounds
- The ability to **formalize and prove** statements about polynomial-time computability within this system
- A **meta-theoretical bridge** from provability within the formal system to mathematical truth

### Later Refinements

Tarnlund revised the proof multiple times:
- **2009**: Reorganized into lemma, corollary, and proof sections
- **2013**: Announced conversion to formal proofs suitable for Hilbert's proof theory and automated theorem provers
- **2017**: Ninth edition with further simplifications

## The Error

### Fundamental Flaw: Confusion Between Provability and Truth

**The Primary Error**: The proof conflates **provability within a formal system** with **mathematical truth about computational complexity**.

**Why This Matters**:
- Just because you can prove "SAT is not in P" in a particular formal system doesn't mean this statement is actually true
- The formal system itself might be:
  1. Inconsistent (can prove both P=NP and P≠NP)
  2. Unsound (proves false statements about computation)
  3. Too weak to capture actual computational complexity
  4. Based on assumptions that don't correspond to real computation

### Specific Issues Identified

#### 1. Unclear Formal System

**Critique by Henning Makholm (2008)**:
- The paper is "pithy to the point of sloppiness"
- The formal system and its axioms are not clearly specified
- The relationship between the formal theory and actual Turing machine computation is not rigorously established

#### 2. SAT Redefinition Concerns

Initial critiques suggested:
- The paper may be working with a non-standard definition of SAT
- The problem being solved in the formal system (PFm) may not be the standard Boolean SAT problem
- This would make the result irrelevant to the actual P vs NP question

While purely propositional formalizations of problems like the pigeonhole principle exist, the paper's presentation made it difficult to verify what was actually being formalized.

#### 3. The Soundness Gap

**Critical Issue**: Even if the formal system proves "SAT is not in P," this only matters if:
- The formal system correctly models actual computation
- The axioms are sound (represent true facts about Turing machines)
- The inference rules preserve truth about computational complexity

None of these were rigorously established in the paper.

#### 4. Meta-Theoretical Leap

The argument requires:
1. Proving a statement within a formal system
2. Concluding that the statement is true in reality

This leap requires:
- **Soundness**: The formal system only proves true statements
- **Adequacy**: The formal system can express computational complexity correctly
- **Consistency**: The formal system doesn't prove contradictions

These properties were not proven for Tarnlund's system.

## Why This Approach Cannot Work (General Principle)

### Gödel's Incompleteness and Complexity

There's a fundamental barrier to this approach:

1. **Self-Reference Problem**: Any formal system strong enough to reason about Turing machines can encode questions about its own provability
2. **Incompleteness**: By Gödel's theorems, no consistent formal system can prove all true statements about computation
3. **Complexity Independence**: If P ≠ NP is true, it's likely true for "simple" computational reasons that don't require sophisticated formal systems to establish

### The Oracle Problem

Even if we could formalize computational complexity:
- We would need to prove that no polynomial-time algorithm for SAT exists
- This requires proving a **universal negative** ("for all algorithms...")
- Formal systems struggle with such universal statements about infinite domains
- We would need the formal system to somehow "know" about all possible algorithms

## Broader Context

### Why This Approach Is Tempting

The approach appears promising because:
- Formal logic has been successful in other areas of mathematics
- Hilbert's program sought to formalize all of mathematics
- Modern automated theorem provers have proven complex results
- P vs NP is a mathematical question, so it should be formalizable

### The Critical Distinction: Syntax vs Semantics

- **Syntax**: What can be proven in a formal system (syntactic manipulation of symbols)
- **Semantics**: What is actually true about computation (real algorithms running on real inputs)
- **The Gap**: Bridging syntax and semantics requires soundness proofs, which are difficult and domain-specific

Tarnlund's error was assuming this gap could be easily bridged without rigorous proof.

## Reception and Legacy

The claim has been:
- **Critiqued**: By Henning Makholm and others in 2008
- **Revised**: Multiple times by Tarnlund (2009, 2013, 2017)
- **Unaccepted**: The complexity theory community does not accept this as a valid proof
- **Unverified**: No independent verification or acceptance in peer-reviewed venues

The fact that the proof has been revised many times without gaining acceptance suggests fundamental issues rather than minor technical errors.

## Formalization Goals

In this directory, we formalize:

1. **The Basic Claim**: What it means to prove computational complexity results in a formal system
2. **The Soundness Requirement**: Why the formal system must correctly model reality
3. **The Gap**: Where the proof fails (soundness is not established)
4. **Key Lessons**: Why mixing provability and truth is dangerous

The formalization demonstrates that:
- The approach is conceptually clear but technically flawed
- The critical step (proving soundness) is non-trivial and not accomplished
- Without soundness, provability in a formal system tells us nothing about reality

## References

### Primary Sources

- **Original Paper**: Tarnlund, S.-A. (2008). "P is not equal to NP"
  - arXiv:0810.5056v1 [cs.CC] (28 Oct 2008)
  - Available at: https://arxiv.org/abs/0810.5056
- **Revised Version**: Tarnlund, S.-A. (2009). "P is not equal to NP"
  - arXiv:0810.5056v2 [cs.CC] (13 Jul 2009)
- **Later Version**: Tarnlund, S.-A. (2017). "P is not equal to NP" (Ninth edition)
  - DiVA Portal: diva2:1142225

### Critiques

- **Makholm Blog Post**: Makholm, H. (2008). "Does P equal NP? This is not an answer"
  - What the Hedgehog Sang blog
  - Available at: http://blog.henning.makholm.net/2008/11/does-p-equal-np-this-is-not-answer.html
- **Schneier Commentary**: Schneier, B. (2008). Noted that "these sorts of papers make the rounds regularly" and recommended skepticism

### Context

- **Woeginger's List**: Entry #48
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **arXiv Category**: Computer Science - Computational Complexity (cs.CC)

## Key Lessons

1. **Provability ≠ Truth**: Proving something in a formal system doesn't make it true in reality
2. **Soundness is Critical**: Formal systems must be proven sound for their domain
3. **Gödel's Limitations**: Formal systems have inherent limitations in what they can prove
4. **Clarity Matters**: Vague formal systems make verification impossible
5. **Peer Review**: Unreviewed claims, especially revised many times, require skepticism
6. **Meta-Theory is Hard**: Reasoning about what formal systems can prove is subtle

## See Also

- [P ≠ NP Framework](../../p_neq_np/) - General framework for evaluating P ≠ NP claims
- [Proof Experiments](../../experiments/) - Other experimental approaches to P vs NP
- [Repository README](../../../README.md) - Overview of the P vs NP problem
