# Peng Cui (2014) - P=NP Claim

**Attempt ID**: 98 (Woeginger's list) / 103 (extended list)
**Author**: Peng Cui
**Year**: 2014
**Claim**: P = NP
**Source**: [arXiv:1401.6520](https://arxiv.org/abs/1401.6520)
**Woeginger's List**: Entry #98 at https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
**Status**: Refuted

## Summary

In January 2014, Peng Cui published a paper titled "Approximation Resistance by Disguising
Biased Distributions" claiming to prove P=NP. The paper claims to solve the Gap problem of
3-XOR using a semidefinite programming (SDP) algorithm and concludes that this implies P=NP.

The paper went through 24 versions on arXiv (versions v2 and v21 were withdrawn), indicating
ongoing difficulties with the manuscript. It has not been accepted by the computational
complexity theory community.

## Main Argument

The paper's main technical ingredients include:

1. **Dictator Test Techniques**: Disguising the verifier's questions using a balanced pairwise
   independent distribution to prevent provers from exploiting the test structure.

2. **Variance-Style Theorem**: Uses a variance-style theorem to eliminate correlation of answers
   of all players based on Label-Cover and its reflection version, forcing optimal strategies
   to use dictator functions.

3. **Three Truncated Biased Pairwise Independent Distributions**: Three specific distributions
   over {-1,1}³ that are pairwise independent with specific biases, used in the PCP verifier.

4. **SDP Algorithm**: Claims that running Charikar & Wirth's SDP algorithm for two rounds on
   the gap problem of 3-XOR proves that this NP-hard problem can be solved efficiently.

5. **No Direct Sum Technique**: The approach avoids the technique of direct sum that requires
   the subgroup property.

The core claim is that the 2-round Charikar-Wirth SDP can **exactly** solve Gap-3-XOR, which
is NP-hard by the PCP theorem. This would demonstrate P=NP.

## The Error

### Fatal Flaw: Approximation vs. Exact Solution

**The error**: The Charikar-Wirth SDP algorithm provides an **approximation**, not an exact
solution to Gap-3-XOR.

**What the SDP actually does:**
- Achieves approximation ratio Ω(k/2^k · log k) above random for Max-k-CSP
- For 3-XOR (k=3): approximately Ω(log 3/8) ≈ 0.137 above the 1/2 baseline
- Runs in polynomial time (interior-point method)

**What would be needed for P=NP:**
- Exact YES/NO decision for Gap-3-XOR instances
- Distinguishing instances where ≥(1-ε)-fraction is satisfiable from those where ≤(1/2+ε)
- No polynomial-time algorithm can do this unless P = NP (Hastad's theorem, JACM 2001)

### The Circular Structure

The argument is circular:
- Gap-3-XOR is NP-hard (proven fact, consequence of PCP theorem)
- Solving Gap-3-XOR in polynomial time ≡ P = NP
- Cui claims the SDP solves Gap-3-XOR exactly (unproven assertion)
- This is equivalent to asserting P = NP, not proving it

### The Tools Are Used Backwards

The paper's technical machinery (disguising technique, variance-style theorem, Label-Cover
reductions) consists of standard **hardness-of-approximation** tools:
- They are used to **prove NP-hardness** of approximation problems
- They do NOT provide polynomial-time algorithms for the resulting hard problems
- Using hardness proof tools and then claiming the hard problem is easy is contradictory

### Supporting Evidence

- **24 arXiv versions**: versions v2 and v21 withdrawn — consistent with repeated failed
  attempts to repair a fundamental flaw
- **6 pages**: Far too short for a proof of such a fundamental result
- **No peer review**: Not published in any peer-reviewed venue
- **No community acceptance**: No major complexity theorist has validated the proof

## Formalization

The formalization is organized in:

- `ORIGINAL.md` — Markdown reconstruction of the paper content
- `ORIGINAL.pdf` — Original paper PDF
- `proof/` — Forward formalization following Cui's claimed argument
  - `lean/CuiProof.lean` — Lean 4 formalization
  - `rocq/CuiProof.v` — Rocq formalization
- `refutation/` — Formalization of why the proof fails
  - `lean/CuiRefutation.lean` — Lean 4 formalization
  - `rocq/CuiRefutation.v` — Rocq formalization

The formalization demonstrates:
1. Gap-3-XOR is NP-hard (axiom, true by Hastad's theorem)
2. Cui's core claim (2-round SDP solves Gap-3-XOR exactly) cannot be proven —
   marked as `axiom`/`Axiom` in the proof files, as it is almost certainly false
3. The logical structure of the proof is valid conditioned on the false claim
4. The refutation identifies exactly where and why the argument fails

## References

- **Paper**: Peng Cui, "Approximation Resistance by Disguising Biased Distributions",
  arXiv:1401.6520, 2014. https://arxiv.org/abs/1401.6520

- **Hastad's Inapproximability**: J. Håstad, "Some optimal inapproximability results,"
  JACM 48(4):798-859, 2001.

- **Charikar-Wirth**: M. Charikar and A. Wirth, "Maximizing quadratic programs:
  extending Grothendieck's inequality," FOCS 2004, pp. 54-60.

- **PCP Theorem**: S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy,
  "Proof verification and the hardness of approximation problems," JACM 45(3):501-555, 1998.

- **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Parent Issue

Part of #44 - Test all P vs NP attempts formally
