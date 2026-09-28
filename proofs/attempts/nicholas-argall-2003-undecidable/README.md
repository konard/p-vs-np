# Nicholas Argall (2003) - P=NP is Undecidable

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Attempts](../README.md)

---

## Metadata

- **Attempt ID**: 8
- **Author**: Nicholas Argall
- **Date**: 25 March 2003
- **Claim**: undecidable / unprovable status for the P versus NP question
- **Status**: **REFUTED** - the argument confuses formal expressibility with formal completeness and does not establish ZFC independence
- **Source**: [Woeginger's P-versus-NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), entry #8

## Summary

Woeginger records Argall's short argument as follows: a provable answer to the P=NP question allegedly requires a complete and consistent formal statement of that question; by invoking Goedel's theorem, Argall concludes that P=NP is undecidable.

The source ASCII file linked from Woeginger's page is no longer retrievable from the current live site. The `original/` directory therefore contains a reconstruction from Woeginger's entry rather than a verbatim archival copy.

## Main Argument

The reconstructed argument has three steps:

1. If P=NP has a provable answer, then the question must have a complete and consistent formal statement.
2. Goedel's incompleteness theorem says that no sufficiently strong consistent formal system is complete.
3. Therefore P=NP has no provable answer, so it is undecidable.

## Formal Error

The critical gap is the first step. A mathematical statement can be precisely formalized in an incomplete theory without requiring the theory to decide that statement. Completeness of the ambient formal system is not a prerequisite for a statement to be meaningful or for the system to prove some particular theorem.

Goedel's theorem gives a conditional metatheorem: every sufficiently strong, effectively axiomatized, consistent theory has some undecidable sentence. It does not imply that an arbitrary sentence expressible in the theory, such as P=NP, is undecidable.

To prove that P=NP is independent of a formal theory such as ZFC, one would need at least:

1. A precise formal sentence representing P=NP in that theory.
2. A proof that the theory does not prove that sentence.
3. A proof that the theory does not prove its negation.

Equivalently, under appropriate soundness/completeness assumptions, one would need model-theoretic witnesses for both sides. Argall's argument provides none of these.

## Formalization

- [Proof notes in Lean](proof/lean/ArgallProof.lean) encode the claimed inference as axioms and mark the missing theorem.
- [Proof notes in Rocq](proof/rocq/ArgallProof.v) mirror the forward argument and isolate the invalid step as an explicit bridge assumption.
- [Refutation in Lean](refutation/lean/ArgallRefutation.lean) proves that expressibility plus incompleteness does not imply independence.
- [Refutation in Rocq](refutation/rocq/ArgallRefutation.v) gives the same structural refutation.

## References

- Gerhard J. Woeginger, "The P-versus-NP page", entry #8.
- Kurt Goedel, "On Formally Undecidable Propositions of Principia Mathematica and Related Systems I", 1931.
- Scott Aaronson, "Is P Versus NP Formally Independent?"

**Part of**: [Issue #558](https://github.com/konard/p-vs-np/issues/558) | **Parent Issue**: [#44](https://github.com/konard/p-vs-np/issues/44)
