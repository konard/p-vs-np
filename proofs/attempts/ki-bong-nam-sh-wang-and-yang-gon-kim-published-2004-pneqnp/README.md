# Ki-Bong Nam, S.H. Wang, and Yang Gon Kim (2004) - P≠NP Attempt

**Attempt ID**: 9 (from Woeginger's list)
**Authors**: Ki-Bong Nam, S.H. Wang, and Yang Gon Kim
**Year**: 2004
**Claim**: P ≠ NP
**Status**: **Refuted** - Error identified in review

## Paper Information

**Title**: Linear Algebra, Lie Algebra and their applications to P versus NP

**Publication**: Journal of Applied Algebra and Discrete Structures, Volume 2, pages 1-26 (2004)
**Publisher**: SAS Int. Publ., Delhi, India

**Review**: MR2038228 (2005e:68070) by Richard K. Molnar in AMS Mathematical Reviews

## Summary

This paper attempts to prove P ≠ NP by defining a counting problem that the authors claim serves as a counterexample to P=NP. The approach uses techniques from linear algebra and Lie algebra, involving systems of linear equations that contain both deterministic data and random variables.

## Main Argument

The authors' approach involves:

1. **Counting Problem Definition**: The paper defines a specific counting problem related to systems of linear equations
2. **Algebraic Framework**: Uses linear algebra and Lie algebra as the mathematical foundation
3. **Non-computability Claim**: Asserts that the relevant system of equations cannot be solved in polynomial time
4. **Key Assertion**: Claims that because the system contains "expressions not just determined from the data but also random variables," it cannot be computed in polynomial time

## Known Refutation

Richard K. Molnar's review in AMS Mathematical Reviews (MR2038228) identifies critical flaws:

### The Core Error

The reviewer states:

> "The crux is the assertion that the problem is not solvable in polynomial time because the relevant system of equations contains expressions not just determined from the data but also random variables. The calculations are lengthy, complex, and difficult to follow, and the assertion of non-computability in polynomial time is not convincing to the reviewer."

### Issues Identified

1. **Lack of Rigorous Proof**: The paper fails to rigorously demonstrate that the problem is not solvable in polynomial time
2. **Unjustified Complexity Claim**: The presence of random variables in the equations is not sufficient justification for non-polynomial-time complexity
3. **Computational Complexity Gap**: No formal proof that the specific counting problem requires super-polynomial time
4. **Obscure Presentation**: The calculations are described as "lengthy, complex, and difficult to follow"

## Error Analysis

### Critical Flaw: Insufficient Lower Bound

The fundamental error is the **lack of a rigorous lower bound proof**. The authors:

1. Define a counting problem involving systems of equations with random variables
2. Assert (without adequate proof) that this problem cannot be solved in polynomial time
3. Fail to provide a formal complexity-theoretic argument for the lower bound

### Why the Argument Fails

**Missing Component**: A valid P ≠ NP proof requires showing that for some problem L in NP, **no** polynomial-time algorithm can solve L. This requires:
- Proving a super-polynomial lower bound on any algorithm for L
- This is exactly what makes P vs NP so difficult

**What the Paper Actually Does**:
- Defines a problem involving random variables
- Claims (without proof) it's hard
- Does not establish that the problem is in NP
- Does not prove a lower bound against all polynomial-time algorithms

**The Gap**: The paper confuses "problem appears complex" with "problem provably requires super-polynomial time." These are fundamentally different:
- A problem can have complex structure yet still be solvable efficiently
- Proving impossibility of efficient algorithms requires techniques that avoid known barriers (relativization, natural proofs, algebrization)

## Formalization Strategy

Our formal verification attempts to capture:

1. **Problem Definition**: Formalize the counting problem the authors propose
2. **The Claimed Lower Bound**: Formalize the assertion that it requires super-polynomial time
3. **The Gap**: Show that the assertion is unproven - we cannot derive the lower bound from the given premises
4. **The Error**: Demonstrate that presence of random variables alone does not imply computational hardness

## Formal Verification

We formalize this attempt in three proof assistants to identify exactly where the logical gap occurs:

- **Coq** (`coq/`): Uses computational types and complexity definitions
- **Lean 4** (`lean/`): Leverages dependent type theory for computational complexity
- **Isabelle/HOL** (`isabelle/`): Uses higher-order logic for algorithm analysis

### Expected Outcome

Each formalization should reveal that:
1. The counting problem can be defined
2. The assertion "this problem is not in P" cannot be derived without additional proof
3. The presence of random variables is not sufficient to establish computational hardness
4. A formal lower bound proof is missing

## References

1. **Original Paper**: Ki-Bong Nam, S.H. Wang, and Yang Gon Kim. "Linear Algebra, Lie Algebra and their applications to P versus NP." *Journal of Applied Algebra and Discrete Structures*, Volume 2, pages 1-26, 2004.

2. **Review**: Richard K. Molnar. MR2038228 (2005e:68070). *AMS Mathematical Reviews*, 2005.

3. **Woeginger's List**: Gerhard J. Woeginger. "The P-versus-NP page." Entry #9. https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Related Work

This attempt is part of a broader pattern of failed P vs NP proofs that:
- Define a specific problem instance
- Assert (without rigorous proof) that it's computationally hard
- Fail to establish formal lower bounds that would survive peer review

Understanding why these approaches fail helps illuminate what a valid proof would require.

## Lessons Learned

1. **Complexity assertions require proof**: Claiming a problem is hard is not the same as proving it
2. **Lower bounds are difficult**: Proving super-polynomial lower bounds is the core challenge of P vs NP
3. **Barriers exist for good reasons**: Techniques like relativization, natural proofs, and algebrization show why simple approaches fail
4. **Formal verification helps**: Attempting to formalize such proofs quickly reveals logical gaps

---

*This formalization is part of Issue #81 in the P vs NP research repository, which systematically examines claimed proofs to understand common errors and improve formal verification techniques.*
