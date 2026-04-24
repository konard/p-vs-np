# Vinay Deolalikar (2010) - P≠NP Attempt

**Attempt ID**: 65
**Author**: Vinay Deolalikar
**Year**: 2010
**Claim**: P ≠ NP
**Status**: Refuted

## Summary

In August 2010, Vinay Deolalikar, a researcher at HP Labs, circulated a 66-page manuscript claiming to prove that P is not equal to NP. This became one of the most high-profile and widely discussed P vs NP proof attempts in history, receiving immediate attention from leading complexity theorists including Terence Tao, Scott Aaronson, and Dick Lipton.

The manuscript was never formally published in a peer-reviewed venue. Multiple fatal flaws were identified within days of the manuscript being circulated.

## Main Argument

### The Approach

Deolalikar's proof strategy combined two areas of mathematics:

1. **Finite Model Theory**: Using descriptive complexity to characterize P — specifically, using results that relate polynomial-time computation to first-order logic with a least-fixed-point operator (LFP) over ordered structures.

2. **Statistical Physics / Random k-SAT**: Using properties of random k-SAT instances and their solution structures, particularly drawing on the theory of the "clustering" or "shattering" phase transition in random constraint satisfaction problems.

### Key Technical Claims

1. **FMC characterization**: Polynomial time (P) corresponds to problems definable in FO+LFP (first-order logic with least fixed point) over ordered structures.

2. **Solution space structure**: Random k-SAT instances in the hard phase (near the satisfiability threshold) have solution spaces with complex clustering structure — solutions are organized into well-separated clusters.

3. **Independence property**: Deolalikar claimed that in these hard-phase instances, solutions have a certain "independence" or "polylog-parameterizability" property: their components can be described using only a polylogarithmic number of parameters drawn independently from a product distribution.

4. **P cannot capture this**: He argued that any FO+LFP query over ordered structures would impose a tree-like structure on the solution space that conflicts with the complex clustering structure observed in hard k-SAT instances.

5. **NP-completeness of k-SAT**: Since k-SAT is NP-complete, its solutions not being capturable in polynomial time would imply P ≠ NP.

### Paper Structure

- **Section 1**: Introduction and statement of main theorem
- **Section 2**: Background on computational complexity (P, NP, Cook-Levin theorem)
- **Section 3**: Finite model theory and descriptive complexity (FO+LFP characterization of P)
- **Section 4**: Parameterized complexity background
- **Section 5**: Statistical physics of random k-SAT (Gibbs measures, clustering, belief propagation)
- **Section 6**: The main argument connecting solution space structure to definability
- **Section 7**: Details of the independence/separability claim
- **Section 8**: Conclusions

## The Errors

The proof had multiple independently fatal flaws, identified rapidly by the research community:

### Error 1: FO+LFP Does Not Capture P Over All Structures

The manuscript relied on the fact that over **ordered** structures, FO+LFP captures exactly P (by Immerman-Vardi theorem). However, the random k-SAT formula as used by Deolalikar is not presented as an **ordered** structure in the relevant sense. The argument tacitly applies the ordered-structure theorem to an unordered or differently-ordered context, which is invalid.

### Error 2: Confusion Between Different k-SAT Distributions

The manuscript conflates properties of the uniform random k-SAT distribution (a specific distribution) with properties of all k-SAT instances. Even if the statistical physics argument were valid for random instances, this does not translate directly to a statement about all NP instances or about the complexity class NP as a whole.

### Error 3: The Polylog-Parameterizability Claim Is Unsubstantiated

The central claim — that solutions to hard k-SAT instances cannot be described by a polylogarithmic number of independent parameters — was never rigorously established. Terence Tao noted that this claim requires showing a lower bound on parameterization complexity that was not proved. Moreover, counterexamples showing that certain structured solution spaces can be parameterized in unexpected ways were pointed out.

### Error 4: The Transfer Argument Fails

Even granting the solution-space structure claims, the argument that FO+LFP formulas must produce solution spaces with tree-like (low-treewidth) structure was disputed. The connection between Gaifman locality of FO+LFP and the global structure of the k-SAT solution space was not established rigorously.

### Error 5: Circular Reasoning in Complexity Arguments

Parts of the argument appeared to assume certain complexity-theoretic separations in order to prove the desired separation — a form of circular reasoning identified by multiple reviewers.

## Community Response

The manuscript was analyzed extensively in real-time on blogs and in emails:

- **Terence Tao**: Identified multiple gaps, particularly in the parameterizability claims and the transfer argument
- **Scott Aaronson**: Noted the FO+LFP vs. unordered structures issue and expressed skepticism about the core argument
- **Dick Lipton**: Hosted extensive blog discussions analyzing each section
- **Neil Immerman**: (co-inventor of FO+LFP characterization) noted issues with how his theorem was being applied
- **Russell Impagliazzo**: Identified issues with the statistical physics argument
- **Piotr Indyk, Madhu Sudan**, and many others: Identified additional gaps

Deolalikar released several revised versions but was unable to address the fundamental criticisms. The proof is now widely regarded as incorrect.

## Formalization Status

- [x] README.md: Present
- [x] ORIGINAL.md: Present
- [ ] ORIGINAL.pdf: Not available (manuscript never formally published)
- [x] proof/ directory: Present (Lean and Rocq)
- [x] refutation/ directory: Present (Lean and Rocq)

## References

- [Wikipedia: Vinay Deolalikar](https://en.wikipedia.org/wiki/Vinay_Deolalikar#Claimed_proof_that_P_%E2%89%A0_NP)
- [Dick Lipton's blog coverage](https://rjlipton.wordpress.com/2010/08/08/a-proof-that-p-is-not-equal-to-np/)
- [Terence Tao's blog analysis](https://terrytao.wordpress.com/2010/08/10/on-deolalikar%E2%80%99s-attempted-proof-that-p%E2%89%A0np/)
- [Scott Aaronson's analysis](https://www.scottaaronson.com/blog/?p=456)
- [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## See Also

- [Parent issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue tracking this attempt](https://github.com/konard/p-vs-np/issues/482)

---

*Created: 2025-10-17*
*Last updated: 2026-04-23*
