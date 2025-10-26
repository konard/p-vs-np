# Peng Cui (2014) - P=NP Attempt

**Attempt ID**: 98
**Author**: Peng Cui
**Year**: 2014
**Claim**: P=NP
**Paper**: "Approximation Resistance by Disguising Biased Distributions"
**ArXiv**: [arXiv:1401.6520](https://arxiv.org/abs/1401.6520)
**Status**: Refuted/Invalid

## Summary

In February 2014, Peng Cui published a paper claiming to prove P=NP. The paper's abstract states:

> "the author shows that the gap problem of some 3-XOR is NP-hard and can be solved by running Charikar&Wirth's SDP algorithm for two rounds. To conclude, the author proves that P=NP."

The main ingredients of the claimed proof include:
- A key issue in dictator test that disguises the questions of the verifier to a balanced pairwise independent distribution
- A variance-style theorem to eliminate correlation of answers of all players
- Based on Label-Cover and its reflection version
- Does not rely on the technique of direct sum that requires the subgroup property
- Claims that a gap problem of k-CSP can be solved using a SDP algorithm in polynomial time

## Main Argument/Approach

The paper attempts to prove P=NP through the following strategy:

1. **3-XOR Gap Problem**: The author considers a specific 3-XOR constraint satisfaction problem (CSP) and its gap version
2. **NP-hardness**: Claims that this particular gap problem is NP-hard
3. **SDP Algorithm**: Claims that running the Charikar & Wirth semidefinite programming (SDP) algorithm for two rounds solves this NP-hard gap problem in polynomial time
4. **Conclusion**: Since an NP-hard problem can be solved in polynomial time, P=NP

The technical approach involves:
- Dictator tests with disguised biased distributions
- Pairwise independent distributions
- Variance-based analysis to handle player correlation
- Label-Cover problem and its reflection

## Critical Flaws

This proof attempt contains fundamental logical and technical errors:

### 1. Circular Reasoning / Invalid Logic
The most fundamental flaw is the logical structure. If P=NP, then ALL problems in NP (including all NP-hard problems) can be solved in polynomial time. However, the author's logic is reversed:
- The paper assumes it has found a polynomial-time algorithm for an NP-hard problem
- But NP-hardness is defined **relative to the assumption that P≠NP**
- If the gap problem is truly solvable in polynomial time, it would simply mean that this particular problem is in P, not that P=NP
- The author would need to prove that this specific problem is NP-complete AND that their algorithm correctly solves it in polynomial time

### 2. Misunderstanding of Approximation Algorithms
- Semidefinite programming algorithms like Charikar & Wirth's are approximation algorithms with performance guarantees
- They don't necessarily solve the **exact** decision problem in polynomial time
- The gap between approximation and exact solution is crucial for complexity theory
- Many NP-hard problems have polynomial-time approximation algorithms, but this doesn't imply P=NP

### 3. Gap Problem vs. Decision Problem
- The paper focuses on a "gap problem" which is a promise problem
- Promise problems have different complexity characteristics than standard decision problems
- Solving a gap version of a problem doesn't necessarily mean solving the original problem
- The reduction from general NP problems to this specific gap problem may not be valid

### 4. Lack of Rigorous Proof
- The paper doesn't provide a complete, rigorous proof that the algorithm correctly solves the problem
- The analysis of the dictator test and correlation elimination is incomplete
- No formal verification of the claimed polynomial-time complexity
- Missing critical details about how the algorithm handles all cases

### 5. Ignores Known Barriers
- The Natural Proofs barrier (Razborov-Rudich, 1997) suggests that certain types of techniques cannot resolve P vs NP
- The Algebrization barrier (Aaronson-Wigderson, 2008) further restricts possible proof techniques
- The paper doesn't acknowledge or address these fundamental barriers
- An SDP-based approach would likely face these barriers

## The Error in the Proof

**Primary Error**: The fundamental error is a logical fallacy in the proof structure. The paper conflates:
1. Having an algorithm that might solve a specific instance or approximation
2. Proving that an NP-complete problem can be solved exactly in polynomial time for ALL instances

The correct logical chain required for proving P=NP would be:
1. Choose an NP-complete problem (e.g., 3-SAT, not a gap variant)
2. Prove that your algorithm solves ALL instances correctly
3. Prove that your algorithm runs in polynomial time for ALL instances
4. Conclude P=NP

Instead, the paper appears to:
1. Define a specific gap problem
2. Claim it's NP-hard (without complete proof)
3. Claim an SDP algorithm solves it (without complete correctness proof)
4. Jump to P=NP conclusion

**Secondary Errors**:
- Incomplete proof of NP-hardness for the specific gap problem
- Incomplete proof that the SDP algorithm solves the problem correctly
- Misunderstanding of the relationship between approximation and exact algorithms
- Missing analysis of all edge cases and problem instances

## Formal Verification Goal

The formal verification in this directory aims to:
1. Model the key components of Cui's approach (dictator tests, Label-Cover, SDP algorithms)
2. Formalize the claimed properties and theorems
3. Identify where the logical gaps and errors occur
4. Demonstrate that the proof does not establish P=NP

Through formalization in Coq, Lean, and Isabelle, we make explicit:
- What assumptions are being made
- Where proofs are incomplete or invalid
- Why the conclusion doesn't follow from the premises

## Related Work

- **Charikar & Wirth's SDP Algorithm**: A legitimate approximation algorithm for certain optimization problems
- **Label-Cover Problem**: A well-studied problem in complexity theory, used in PCP theorem and hardness of approximation
- **Dictator Tests**: Used in analysis of constraint satisfaction problems and PCP constructions
- **3-XOR Problem**: A specific CSP studied in approximation algorithms literature

## References

1. Peng Cui (2014). "Approximation Resistance by Disguising Biased Distributions". arXiv:1401.6520
2. Gerhard J. Woeginger's P-versus-NP page: https://www.win.tue.nl/~gwoegi/P-versus-NP.htm (Entry #98)
3. Moses Charikar and Anthony Wirth. "Maximizing quadratic programs: extending Grothendieck's inequality." FOCS 2004
4. Subhash Khot. "On the power of unique 2-prover 1-round games." STOC 2002 (Label-Cover and hardness)

## Status

This proof attempt is **invalid** and does not successfully prove P=NP. The formalization work serves an educational purpose: demonstrating how formal methods can help identify errors in purported proofs of major mathematical conjectures.

---

*Part of the systematic formalization effort for P vs NP proof attempts, tracking issue #44*
