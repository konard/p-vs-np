# Mircea Alexandru Popescu Moscu (2004) - P≠NP Attempt

**Author**: Mircea Alexandru Popescu Moscu (listed as entry #18 on Woeginger's list)
**Year**: November 2004
**Claim**: P ≠ NP
**Paper**: [arXiv:cs.CC/0411033](http://arxiv.org/abs/cs.CC/0411033)
**Title**: "On Invariance and Convergence in Time Complexity theory"

## Summary

In November 2004, Mircea Alexandru Popescu Moscu introduced an invariance principle of complexity hierarchies. The paper claims to prove that P is not equal to NP based on three invariance principles and a convergence theorem.

According to the abstract, the paper:
1. Introduces "three invariance principles under which P is different from NP"
2. Proves a "theorem of convergence" stating that "for any language L there exists an infinite sequence of languages from O(n) that converges to L"

The author suggests the proof holds "if you are willing to believe that the property of a complexity class to be closed or openend to the nondeterministic extension operator it's an invariant of complexity theory."

## Main Argument/Approach

### The Invariance Principle

The proof relies on an **invariance principle of complexity hierarchies**. The central claim is that certain properties of complexity classes should remain invariant under specific transformations or extensions.

Key concepts:
- **Invariance under nondeterministic extension**: The property of a complexity class being closed or open under the nondeterministic extension operator is claimed to be an invariant of complexity theory
- **Convergence theorem**: For any language L, there exists an infinite sequence of languages from O(n) (linear time) that converges to L

### Proof Strategy

The proof attempts to establish P ≠ NP by:

1. **Defining invariance properties**: Establishing that certain structural properties of complexity classes are invariants
2. **Applying the convergence theorem**: Using the convergence of language sequences to relate different complexity classes
3. **Distinguishing P from NP**: Arguing that the invariance properties distinguish P from NP based on their closure properties under nondeterministic extensions

## The Error in the Proof

### Critical Issues

The proof contains several fundamental gaps and errors:

#### 1. **Undefined Invariance Principle**

The paper relies heavily on an "invariance principle" but:
- The exact definition of what constitutes an "invariant of complexity theory" is not rigorously formalized
- The claim that "the property of a complexity class to be closed or openend to the nondeterministic extension operator" is an invariant lacks formal justification
- No proof is provided that this property is indeed invariant under relevant transformations

#### 2. **Circular Reasoning**

The argument appears circular:
- It assumes that certain closure properties distinguish complexity classes
- But these very closure properties are what define P and NP in the first place
- The proof essentially assumes what it attempts to prove: that P and NP have different closure properties under nondeterministic operations

#### 3. **Convergence Theorem Issues**

The convergence theorem states: "for any language L there exists an infinite sequence of languages from O(n) that converges to L"

Problems:
- The notion of "convergence" for languages is not precisely defined
- Even if such convergence exists, it's unclear how this relates to computational complexity
- The theorem doesn't establish any connection to the separation of P and NP
- No formal proof is provided for this convergence theorem

#### 4. **Missing Rigorous Definitions**

The paper lacks:
- Precise mathematical definitions of the invariance principles
- Formal statements of the theorems
- Rigorous proofs connecting the invariance principles to the P vs NP question
- Clear definitions of the "nondeterministic extension operator"

#### 5. **Unjustified Assumptions**

The paper explicitly requires the reader to "believe" that certain properties are invariants, which is not how mathematical proofs work. A valid proof must:
- Formally define all concepts
- Prove (not assume) that properties are invariants
- Rigorously connect these properties to the conclusion

### Core Logical Gap

The fundamental error is that the paper **confuses descriptive properties with separating properties**:
- P and NP have different definitions (deterministic vs nondeterministic)
- The paper attempts to elevate this definitional difference to an "invariance principle"
- But having different definitions doesn't prove that the classes are different
- The P vs NP question is precisely about whether these different definitions yield different classes

In formal terms: The paper assumes that definitional differences imply class separation, which is begging the question.

## Formalization Strategy

Our formalization in Coq, Lean, and Isabelle will:

1. **Define the basic complexity classes** (P, NP) formally
2. **Attempt to formalize the invariance principle** as stated in the paper
3. **Formalize the convergence theorem** with precise definitions
4. **Identify where the proof breaks down** by attempting to connect the invariance principle to P ≠ NP

The formalization will make explicit where assumptions are unjustified and where logical gaps exist.

## References

- Woeginger's P vs NP page: [https://wscor.win.tue.nl/woeginger/P-versus-NP.htm](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #18)
- Paper: [arXiv:cs.CC/0411033](http://arxiv.org/abs/cs.CC/0411033)

## Status

- [x] Folder structure created
- [x] README with analysis created
- [ ] Coq formalization in progress
- [ ] Lean formalization in progress
- [ ] Isabelle formalization in progress
