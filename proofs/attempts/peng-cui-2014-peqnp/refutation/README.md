# Peng Cui (2014) - Refutation

## Why the Proof Fails

Cui's 2014 P=NP attempt contains a fundamental error: **the Charikar-Wirth SDP algorithm
provides an approximation, not an exact solution to Gap-3-XOR**.

## The Fatal Error: Approximation vs. Exact Solution

### The Claim

Cui claimed that running the Charikar-Wirth SDP algorithm for **two rounds** on a specific
Gap-3-XOR instance can solve it **exactly** — i.e., can distinguish:
- **YES instances**: ≥ (1-ε) fraction of clauses satisfiable
- **NO instances**: ≤ (1/2+ε) fraction of clauses satisfiable

### Why This Is Wrong

| Aspect | What Cui Claimed | What Is Actually True |
|--------|------------------|-----------------------|
| **Algorithm output** | Exact YES/NO answer | Approximation ratio |
| **Approximation guarantee** | Exact optimum | Ω(k/2^k · log k) ≈ O(log 3/8) |
| **Gap-3-XOR** | Solvable in poly time | NP-hard (Hastad 2001) |
| **Implication** | P = NP | P ≠ NP (believed) |

### The Charikar-Wirth Algorithm

Charikar and Wirth (FOCS 2004) gave an SDP relaxation for Max-k-CSP. Their algorithm:
1. Formulates Max-k-CSP as a semidefinite program (SDP)
2. Solves the SDP relaxation in polynomial time
3. Rounds the vector solution to a binary assignment

**What it achieves:** An approximation ratio of Ω(k/2^k · log k) above the random
assignment baseline. For 3-XOR (k=3), this is approximately Ω(log(3)/8) ≈ 0.137.

**What it does NOT achieve:** Exact solution to the gap problem. The algorithm may output
a solution that is "good" (above random) but cannot exactly decide whether an instance
is a YES or NO instance of Gap-3-XOR.

### Why Approximation ≠ Exact Solution

To solve Gap-3-XOR in polynomial time, one would need an algorithm that:
- On YES instances (≥ (1-ε) fraction satisfiable): always outputs YES
- On NO instances (≤ (1/2+ε) fraction satisfiable): always outputs NO

The Charikar-Wirth SDP achieves an approximation better than random, but this is not
sufficient to distinguish YES from NO instances. The gap between (1-ε) and (1/2+ε) is
precisely what makes the problem NP-hard.

## The PCP Theorem Connection

The NP-hardness of Gap-3-XOR is a consequence of:

1. **PCP Theorem** (Arora-Lund-Motwani-Sudan-Szegedy 1998; Arora-Safra 1998):
   NP = PCP[log n, 1]

2. **Hastad's 3-bit PCP** (STOC 1997, JACM 2001):
   For any ε > 0, it is NP-hard to distinguish satisfiable 3-XOR instances from
   those where at most (1/2 + ε) fraction can be satisfied.

This hardness result means: **if any polynomial-time algorithm can solve Gap-3-XOR exactly,
then P = NP**. Cui's claim that the SDP does this is equivalent to asserting P = NP,
not proving it.

## The Circular Argument

Cui's proof has a circular structure:
1. Gap-3-XOR is NP-hard (TRUE, by Hastad's theorem)
2. The SDP solves Gap-3-XOR in polynomial time (ASSERTED, not proven)
3. Therefore P = NP (follows from 1+2)

Step 2 is precisely what needs to be proven for the argument to work, but the paper only
asserts it. The disguising technique and variance-style theorem are standard tools in
hardness of approximation — they are used to prove NP-hardness of approximation problems
(upper bounds on what algorithms can do), not to design efficient algorithms.

## The Disguising Technique Problem

The paper's main technical innovation is "disguising" the verifier's questions using
biased pairwise independent distributions. This technique:

- **Is valid** as a tool for constructing PCP verifiers (hardness proofs)
- **Does not** help design efficient algorithms for the resulting problems
- **Is used backwards**: the paper uses a hardness-of-approximation construction
  and then claims the SDP can solve the hard problem

The variance-style theorem and Label-Cover reduction are similarly tools for proving
hardness, not for designing polynomial-time algorithms.

## Multiple Revisions as Evidence

The paper went through 24 versions on arXiv, with versions v2 and v21 withdrawn.
This pattern is consistent with a flawed proof that the author repeatedly attempted
to repair without success.

## Summary

Cui's approach fails because:

1. **The Charikar-Wirth SDP approximates but does not exactly solve Gap-3-XOR**
2. **The disguising technique is a hardness tool, not an algorithmic technique**
3. **The core claim is equivalent to P = NP, not a proof of it**
4. **The PCP theorem guarantees NP-hardness of Gap-3-XOR, which the paper implicitly assumes
   but then contradicts**

## Formal Refutation

See:
- `lean/CuiRefutation.lean` - Lean 4 formalization of the refutation
- `rocq/CuiRefutation.v` - Rocq formalization of the refutation

These formalizations demonstrate:
1. Gap-3-XOR is NP-hard (axiom, true)
2. The Charikar-Wirth SDP only provides an approximation (true, provable)
3. An approximation algorithm cannot solve a promise problem exactly in general
4. Therefore, Cui's core claim cannot be derived from the SDP's properties

## References

- **Hastad's Inapproximability:** J. Håstad, "Some optimal inapproximability results,"
  JACM 48(4):798-859, 2001.

- **Charikar-Wirth:** M. Charikar and A. Wirth, "Maximizing quadratic programs:
  extending Grothendieck's inequality," FOCS 2004, pp. 54-60.

- **PCP Theorem:** S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy,
  "Proof verification and the hardness of approximation problems," JACM 45(3):501-555, 1998.

- **Cui's Paper:** P. Cui, "Approximation Resistance by Disguising Biased Distributions,"
  arXiv:1401.6520, 2014. (24 versions; v2 and v21 withdrawn)
