# Minseong Kim (2012) - P≠NP Attempt

**Author:** Minseong Kim
**Year:** 2012
**Claim:** P≠NP
**Status:** Invalid (Withdrawn)
**Woeginger Entry:** #84

## Summary

In March 2012, Minseong Kim published a paper claiming to prove that the Zermelo-Fraenkel axioms of set theory together with the axiom of choice (ZFC) are inconsistent, and then deduced from this that P is not equal to NP. The paper was titled "Inconsistency of the Zermelo-Fraenkel set theory with the axiom of choice and its effects on the computational complexity" and appeared on arXiv at http://arxiv.org/abs/1203.0494.

## The Main Argument

The attempted proof follows this logical chain:

1. **Claim:** ZFC (Zermelo-Fraenkel set theory with the axiom of choice) is inconsistent
2. **Deduction:** If ZFC is inconsistent, then Peano arithmetic is inconsistent
3. **Consequence:** From an inconsistent foundation, one can derive any statement, including P≠NP

This approach attempts to use *ex falso quodlibet* (from a contradiction, anything follows) to prove P≠NP.

## The Fatal Flaw

The entire proof attempt is fundamentally flawed for multiple critical reasons:

### 1. **ZFC is Not Known to be Inconsistent**

ZFC has been the standard foundation for mathematics for over a century. There is no credible evidence that ZFC is inconsistent. The mathematical community has used ZFC extensively since its formulation, and no contradiction has been found. The claim that ZFC is inconsistent is extraordinary and would require extraordinary evidence.

### 2. **The Paper Was Withdrawn**

The paper itself includes a note stating: **"This paper of course does not make any sense"** and was subsequently withdrawn from serious consideration. The author apparently recognized the fundamental errors in the work.

### 3. **Logical Fallacy: Proof from False Premises**

Even if one could prove P≠NP from an inconsistent foundation, this would be meaningless. In an inconsistent logical system, one can prove both P≠NP and P=NP simultaneously. Such a "proof" carries no mathematical value because:
- From contradiction, everything follows (principle of explosion)
- The proof would not tell us anything about the actual relationship between P and NP
- It would be a vacuous truth, not a genuine mathematical result

### 4. **Circular Reasoning**

The argument assumes what needs to be proven (that mathematics is inconsistent) without providing valid justification. The paper does not contain a rigorous proof of ZFC's inconsistency.

### 5. **Misunderstanding of Mathematical Foundations**

The approach demonstrates a fundamental misunderstanding of:
- How mathematical proofs work
- The role of axiomatic foundations
- The meaning of consistency and inconsistency
- The nature of the P vs NP problem

## Refutation

The refutation is straightforward:

1. **No Valid Proof of ZFC Inconsistency:** The paper does not provide a valid proof that ZFC is inconsistent. ZFC is widely believed to be consistent, and no credible contradiction has been found in over 100 years of use.

2. **Withdrawn by Community:** The mathematical and computer science communities immediately rejected this attempt as invalid.

3. **Meta-mathematical Consideration:** Even if ZFC were inconsistent (which we have no reason to believe), this would not constitute a genuine proof of P≠NP. It would only show that our foundations are flawed, not that P≠NP is true in any meaningful sense.

## Formalization Strategy

Our formalization approach demonstrates the error by:

1. **Explicitly showing the claim of ZFC inconsistency as an axiom (not a proven theorem)**
2. **Demonstrating that from an inconsistent system, both P=NP and P≠NP can be "proven"**
3. **Highlighting that such "proofs" are vacuous and meaningless**

The formalizations in Coq, Lean, and Isabelle will:
- Model the logical structure of the claimed proof
- Explicitly mark the unproven assumption (ZFC inconsistency)
- Show that the conclusion (P≠NP) depends entirely on this false assumption
- Demonstrate the principle of explosion (from falsehood, anything follows)

## Educational Value

This attempt serves as an important educational example of:

1. **Invalid Proof Techniques:** Not all logical derivations constitute valid proofs
2. **The Importance of Sound Foundations:** Mathematical proofs require consistent axiom systems
3. **Critical Analysis:** The need to scrutinize claimed proofs carefully
4. **Meta-mathematical Awareness:** Understanding the difference between proving something within a system versus proving something about a system

## References

- **arXiv Paper:** http://arxiv.org/abs/1203.0494 (withdrawn)
- **Woeginger's P vs NP Page:** https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #84)
- **Source:** Gabriel Istrate provided the link to Woeginger's list

## Implementation Notes

The formalizations in this directory demonstrate:

1. How the claimed proof structure works (as a logical framework)
2. Why the assumption of ZFC inconsistency is unjustified
3. How the principle of explosion makes such proofs meaningless
4. The difference between valid and invalid proof methods

Each formalization explicitly comments on where the error occurs and why the proof attempt fails.

## Directory Structure

```
proofs/attempts/minseong-kim-2012-pneqnp/
├── README.md (this file)
├── coq/
│   └── KimAttempt.v (Coq formalization showing the error)
├── lean/
│   └── KimAttempt.lean (Lean formalization showing the error)
└── isabelle/
    └── KimAttempt.thy (Isabelle formalization showing the error)
```

## Conclusion

The Minseong Kim (2012) attempt is not a valid proof of P≠NP. It relies on the false assumption that ZFC is inconsistent and uses flawed reasoning that would make the conclusion meaningless even if the assumption were true. This attempt was properly rejected by the mathematical community and serves primarily as an educational example of invalid proof methodology.

The value of formalizing this attempt lies not in validating the proof (which is impossible), but in:
- Clearly identifying the errors
- Understanding the logical structure of invalid proofs
- Learning to distinguish valid from invalid proof techniques
- Demonstrating the principle of explosion in formal logic
