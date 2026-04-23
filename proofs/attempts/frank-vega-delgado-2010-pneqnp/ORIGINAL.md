# Original Paper: The Existence of One-Way Functions (November 2010)

**Author:** Frank Vega Delgado
**Year:** 2010 (November)
**Title:** "The existence of one-way functions" (November 2010 version)
**Claim:** P ≠ NP
**Woeginger's List:** Entry #68
**Source:** http://the-point-of-view-of-frank.blogspot.com/ (blog post, November 2010)

---

## Note on Availability

The original November 2010 paper by Frank Vega Delgado was published as a blog post at http://the-point-of-view-of-frank.blogspot.com/. It has not been formally published in a peer-reviewed journal, and the exact text may have been revised over time as Vega Delgado continued to update his work. The paper is cited in Woeginger's P-versus-NP list as entry #68 ("In November 2010, Frank Vega Delgado proved that P is not equal to NP"). The February 2012 version (Woeginger #83) developed a different argument using UP ⊆ NP.

---

## Summary of the Claimed Proof (Reconstructed from Available Sources)

The November 2010 approach revolves around the concept of **one-way functions** and their relationship to P vs NP:

### Background: One-Way Functions

A function `f : {0,1}* → {0,1}*` is a **one-way function** if:
1. **Easy to compute**: There exists a polynomial-time algorithm to compute `f(x)` for any input `x`.
2. **Hard to invert**: For any probabilistic polynomial-time algorithm `A`, the probability that `A(f(x), 1^|x|)` outputs any `x'` with `f(x') = f(x)` is negligible (as a function of `|x|`).

### Known Relationship to P vs NP

It is known that:
- If P = NP, then one-way functions do NOT exist (since inverting `f` would be in P)
- The existence of one-way functions would imply P ≠ NP (contrapositive)
- Whether one-way functions exist is itself an open problem

### Vega Delgado's Claimed Argument

The 2010 paper claims to construct or demonstrate the existence of one-way functions without assuming P ≠ NP, thereby proving P ≠ NP via the known implication. Specifically, the argument is:

1. **Construct candidate one-way function**: Define a specific function `f` that is efficiently computable.
2. **Argue hardness of inversion**: Claim (without fully rigorous proof) that inverting `f` is computationally hard even assuming P = NP.
3. **Apply known implication**: If one-way functions exist → P ≠ NP.
4. **Conclusion**: P ≠ NP.

---

## Key Claims in the Paper

1. **Claim A**: A specific function `f` can be computed in polynomial time.
2. **Claim B**: Inverting `f` requires superpolynomial time (even for all of NP).
3. **Claim C**: Therefore, one-way functions exist.
4. **Claim D**: The existence of one-way functions implies P ≠ NP.

---

## Publication History

- The paper was posted to Frank Vega Delgado's blog in November 2010: http://the-point-of-view-of-frank.blogspot.com/
- It was listed as entry #68 on Woeginger's P versus NP list.
- Frank Vega Delgado subsequently revised his approach multiple times, leading to the February 2012 paper (Woeginger #83) and later the June 2015 and February 2016 papers.
- None of these papers have been accepted by the complexity theory community as valid proofs.

---

## References

- Woeginger's P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #68)
- One-way functions: Goldreich, O. (2001). "Foundations of Cryptography: Volume I, Basic Tools." Cambridge University Press.
- P vs NP and one-way functions: Impagliazzo, R. (1995). "A personal view of average-case complexity." Proceedings of the 10th Annual Structure in Complexity Theory Conference.
- Time Hierarchy Theorem: Hartmanis, J., & Stearns, R. E. (1965). "On the computational complexity of algorithms." Transactions of the American Mathematical Society.
