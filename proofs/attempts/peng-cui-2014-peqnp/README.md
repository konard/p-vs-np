# Peng Cui (2014) - P=NP Claim

**Attempt ID**: 98
**Author**: Peng Cui
**Year**: 2014
**Claim**: P = NP
**Source**: [arXiv:1401.6520](https://arxiv.org/abs/1401.6520)
**Woeginger's List**: Entry #98 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Summary

In February 2014, Peng Cui published a paper titled "Approximation Resistance by Disguising Biased Distributions" claiming to prove P=NP. The paper claims to solve the gap problem of 3-XOR using a semidefinite programming (SDP) algorithm and concludes that this implies P=NP.

## Main Argument/Approach

The paper's main technical ingredients include:

1. **Dictator Test Techniques**: The paper addresses a key issue in dictator tests that disguises the questions of the verifier to a balanced pairwise independent distribution.

2. **Variance-Style Theorem**: Uses a variance-style theorem to eliminate correlation of answers of all players based on Label-Cover and its reflection version.

3. **SDP Algorithm**: Claims that running Charikar & Wirth's SDP algorithm for two rounds on the gap problem of some 3-XOR proves that this NP-hard problem can be solved efficiently.

4. **Three Truncated Biased Pairwise Independent Distributions**: The approach uses these distributions as part of the construction.

5. **No Direct Sum Technique**: The approach claims not to rely on the technique of direct sum that requires the subgroup property.

The core claim is that by showing a specific 3-XOR gap problem (which is NP-hard) can be solved by an SDP algorithm in polynomial time, this demonstrates P=NP.

## Critical Analysis

### Issues with the Claim

1. **Extraordinary Claim**: The claim of proving P=NP is extraordinary and would represent one of the most significant mathematical discoveries of all time. Such claims require extraordinary scrutiny.

2. **Paper Length**: The paper is only 6 pages long, which is remarkably brief for resolving such a fundamental and difficult problem. Most serious attempts at major complexity theory results span dozens or hundreds of pages.

3. **Multiple Revisions**: The arXiv listing shows 24 versions of the paper, including withdrawn versions (v2 and v21), suggesting ongoing issues with the manuscript's claims or methodology.

4. **No Peer Review**: The paper appears only on arXiv and has not been published in a peer-reviewed journal or conference, which is typical for flawed P vs NP proofs.

5. **Lack of Acceptance**: The result has not been accepted by the computational complexity theory community, and no major researchers have validated the proof.

### Likely Error

The most likely error in this type of argument is a gap between:
- Showing that a specific SDP algorithm can solve a specific instance or restricted version of 3-XOR efficiently, versus
- Showing that all NP-complete problems (or equivalently, all instances of 3-SAT/3-XOR in their full generality) can be solved in polynomial time.

Common errors in P=NP claims include:
- Solving a related but easier problem
- Missing subtle conditions or assumptions
- Incorrect complexity analysis
- Confusing average-case with worst-case complexity
- Errors in the reduction or hardness proof

Without access to the full paper details, we cannot pinpoint the exact error, but the formalization process below aims to identify where the argument fails.

## Formalization Goals

This formalization aims to:

1. Formalize the key definitions (3-XOR, gap problems, SDP algorithms)
2. Formalize the claimed algorithm and its properties
3. Formalize the claimed reduction or proof that this implies P=NP
4. Identify the gap or error in the argument through formal verification

The formalization will be done in three proof assistants:
- **Rocq** (`rocq/PengCui2014.v`)
- **Lean** (`lean/PengCui2014.lean`)
- **Isabelle/HOL** (`isabelle/PengCui2014.thy`)

## Status

This formalization is part of the systematic effort (issue #44) to formally verify or refute claimed proofs of P vs NP. The goal is not to prove or disprove P vs NP itself, but to understand and formalize the specific claims made in this paper and identify where the error lies.

## References

- **Paper**: Peng Cui, "Approximation Resistance by Disguising Biased Distributions", arXiv:1401.6520, 2014
- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Charikar & Wirth SDP**: Moses Charikar and Anthony Wirth, "Maximizing quadratic programs: extending Grothendieck's inequality", FOCS 2004

## Parent Issue

Part of #44 - Test all P vs NP attempts formally
