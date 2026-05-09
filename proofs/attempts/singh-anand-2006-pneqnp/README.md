# Bhupinder Singh Anand (2006) - P≠NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Woeginger's List Entry #27](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

---

## Metadata

- **Attempt ID**: 27 (from Woeginger's list)
- **Author**: Bhupinder Singh Anand
- **Year**: 2006 (revised February 2007)
- **Claim**: P ≠ NP
- **Paper Title**: "An elementary proof that P ≠ NP"
- **Source**: [arXiv:math/0603605](http://arxiv.org/abs/math.GM/0603605)

---

## Quick Links

- **[Original Paper (ORIGINAL.md)](./ORIGINAL.md)** - Reconstruction of the paper's content
- **[Proof Attempt (proof/)](./proof/)** - Formalization of Anand's argument
- **[Refutation (refutation/)](./refutation/)** - Why the proof fails

---

## Summary

Bhupinder Singh Anand's 2006 paper claims to prove P ≠ NP through an argument about non-standard models of Peano Arithmetic (PA). The proof proceeds in two steps:

1. **Step 1**: If PA has no non-standard models, then P ≠ NP.
2. **Step 2**: PA has no non-standard models (claimed via an induction argument).
3. **Conclusion**: Therefore, P ≠ NP.

### The Main Claim

The paper defines the formula:
```
G(x) := [x = 0 ∨ ¬(∀y)¬(x = y')]
```
meaning "x is 0 or x is the successor of some element." The author proves (∀x)G(x) in PA by induction, then incorrectly concludes this eliminates non-standard models.

---

## The Fatal Error

### The Error

The proof **confuses provability within PA with truth only in the standard model**.

Specifically: the author proves (∀x)G(x) in PA and concludes PA has no non-standard models. But by **Gödel's Completeness Theorem**, if a formula is provable in PA, it is true in **all** models of PA—both standard and non-standard.

In non-standard models, the non-standard "infinite" elements each have a predecessor (another non-standard element), so G(x) holds for them too. The formula (∀x)G(x) does not exclude non-standard models; it merely tells us every element (including non-standard ones) is either 0 or a successor.

### Why It Fails

1. **Gödel's Completeness Theorem**: Provable formulas hold in ALL models, including non-standard ones. Proving (∀x)G(x) does not eliminate non-standard models.

2. **Gödel's Incompleteness Theorem + Löwenheim-Skolem Theorem**: These results together **guarantee** that first-order PA has non-standard models. The author's conclusion contradicts established mathematics.

3. **Non-standard elements satisfy G(x)**: In a non-standard model, each non-standard element ω has a predecessor ω-1 (also non-standard), so ω = S(ω-1), making G(ω) true. The non-standard elements form infinite descending chains—they all satisfy G(x).

4. **No complexity analysis**: Even if the model-theory argument were correct, the paper provides no rigorous connection between PA model structure and polynomial-time computation.

---

## Error Classification

| Error Type | Description |
|---|---|
| **Primary error** | Confusion between provability in PA and truth only in the standard model |
| **Secondary error** | Contradicts Gödel's Incompleteness Theorem and Löwenheim-Skolem Theorem |
| **Tertiary error** | No rigorous connection between PA models and computational complexity |

---

## Status

- ✅ Error identified: Confusing provability with model elimination
- ✅ Original paper reconstructed in ORIGINAL.md
- ✅ Lean formalization: Complete (proof/ and refutation/)
- ✅ Rocq formalization: Complete (proof/ and refutation/)

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Task Description](../../../P_VS_NP_TASK_DESCRIPTION.md)
