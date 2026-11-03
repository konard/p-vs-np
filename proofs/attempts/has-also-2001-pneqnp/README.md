# Seenil Gram (2001): "EXP ⊆ NP" Claim

**Attempt ID**: 5 (from Woeginger's list)
**Author**: Seenil Gram (pseudonym "has also")
**Year**: 2001
**Claim**: P ≠ NP (derived from the stronger claim that EXP ⊆ NP)
**Status**: Informal/unverified analysis. The claimed corollary rests on an
unpublished lemma that has not been examined here. Not refuted.

> **Correction (2026-11-03).** Earlier versions of this README and of the
> Lean and Rocq files called EXP ⊆ NP "provably false" and "a contradiction
> with the Time Hierarchy Theorem". That is wrong. EXP ⊆ NP is equivalent to
> NP = EXP, which is an open question. The hierarchy theorems give P ⊊ EXP
> and NP ⊊ NEXP, and neither rules out NP = EXP. The "direct refutation" in
> the old text used the language {⟨M, x, 1^(2^n)⟩ : M accepts x within 2^n
> steps}. Its padding makes it decidable in time polynomial in its own input
> length, so it is in P, not an example of a language outside NP. The formal
> files in `lean/` and `rocq/` encode the old argument with unproved axioms
> (one of them, that an EXPTIME-complete language is outside NP, is an open
> problem stated as an axiom). They are historical sketches and refute
> nothing.

## Source

**Paper**: "Redundancy, Obscurity, Self-Containment & Independence"
**Published in**: Proceedings of the 3rd International Conference on Information and Communications Security (ICICS 2001)
**Location**: Xian, China, November 13-16, 2001
**Publisher**: Springer Lecture Notes in Computer Science, Volume 2229, pages 495-501
**Reference**: Listed as entry #5 on [Woeginger's P vs NP attempts page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## Summary of the Claimed Proof

1. The paper proves an "Indistinguishability Lemma". Its details are not
   available to this repository.
2. It states EXP ⊆ NP as "a simple, direct corollary" (page 501).
3. EXP ⊆ NP together with the deterministic time hierarchy (P ⊊ EXP) would
   give P ≠ NP. That implication is valid. The open question is whether the
   lemma and the corollary are correct.

## What is known about EXP ⊆ NP

- NP ⊆ PSPACE ⊆ EXP is known, so EXP ⊆ NP is the same as NP = EXP.
- P ⊊ EXP (Hartmanis and Stearns 1965) and NP ⊊ NEXP (Cook 1973; Seiferas,
  Fischer and Meyer 1978; Žák 1983) are known.
- No known theorem rules out NP = EXP. It is widely believed false, but it
  is open.
- So a claim of EXP ⊆ NP is a claim stronger than P ≠ NP and cannot be
  refuted by citing the hierarchy theorems.

## Type of Error

Unknown. Without the text of the Indistinguishability Lemma no step can be
identified as wrong. Family 19 of
[COMMON_ERRORS.md](../COMMON_ERRORS.md#attempt-coverage-index) (claims
without an examinable argument) records this attempt at the evidence level
"Informal/unverified analysis".

## What would count as progress

- Obtain the paper and transcribe the Indistinguishability Lemma.
- Find a concrete counterexample to the lemma, or name the unproved step as
  an explicit premise (see [REFUTATION_PLAN.md](../REFUTATION_PLAN.md)).
- Replace the axioms in `lean/` and `rocq/` with definitions from
  `proofs/complexity`; never assume EXP ⊄ NP.

## Historical Context

The paper appeared in the proceedings of a security conference (ICICS 2001)
and claims a result stronger than P ≠ NP. Woeginger's list records it. The
lesson for this repository is the one this README itself first got wrong:
check whether a statement is known to be false before calling it false.

## References

1. **Gram, S.** (2001). "Redundancy, Obscurity, Self-Containment & Independence." *Proceedings of ICICS 2001*, LNCS 2229, pp. 495-501. Springer.

2. **Hartmanis, J., & Stearns, R. E.** (1965). "On the computational complexity of algorithms." *Transactions of the American Mathematical Society*, 117, 285-306. DOI: [10.1090/S0002-9947-1965-0170805-7](https://doi.org/10.1090/S0002-9947-1965-0170805-7)

3. **Woeginger, G. J.** "The P versus NP page." Available at: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

4. **Cook, S. A.** (1971). "The complexity of theorem-proving procedures." *Proceedings of the 3rd Annual ACM Symposium on Theory of Computing*, pp. 151-158.

5. **Arora, S., & Barak, B.** (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press. (See Chapter 3 on the Time Hierarchy Theorem)

## Verification Status

- `rocq/GramRefutation.v` and `lean/GramRefutation.lean` are historical
  sketches built on unproved axioms, including an axiom that states an open
  problem. They do not refute the claim. There is no Isabelle file.

## Notes

- The actual paper is difficult to access, as LNCS 2229 is not freely available
- Gram provided "additional explanations" on the sci.crypt newsgroup, but these archives are not readily accessible
- The specific details of the "Indistinguishability Lemma" remain unknown
- This attempt is cataloged on Woeginger's authoritative list of P vs NP proof attempts

## Lessons Learned

1. Before calling a statement false, check that it is known to be false.
   EXP ⊆ NP is open.
2. A padded language such as {⟨M, x, 1^(2^n)⟩} can be easy in its own input
   length; padding changes complexity classes.
3. A valid implication (EXP ⊆ NP and P ⊊ EXP give P ≠ NP) moves all the
   weight onto the premise; examine the premise.
