# Amar Mukherjee (2011) - Refutation

## Why the Proof Fails

Mukherjee's 2011 P=NP attempt — a claimed deterministic polynomial-time algorithm for 3-SAT — was **withdrawn by the author** before it could be formally refuted by the community. The withdrawal itself is the primary evidence of failure.

## The Fundamental Barrier

### 3-SAT is NP-Complete

3-SAT is NP-complete (Cook 1971, Levin 1973). This means:

| Property | 3-SAT |
|----------|-------|
| **Verification** | Given a candidate assignment, verifiable in O(n·m) time (polynomial) |
| **Decision** | No polynomial-time algorithm known |
| **Belief** | Essentially all experts believe no polynomial algorithm exists |
| **Consequence** | Polynomial-time 3-SAT would imply P = NP |

### Why Polynomial-Time 3-SAT Is Extremely Unlikely

1. **Decades of Effort**: Thousands of researchers have tried to find polynomial-time algorithms for 3-SAT (and other NP-complete problems) since 1971, with no success
2. **Natural Barriers**: Several mathematical barriers (relativization, algebrization, natural proofs) prevent large classes of proof techniques from establishing P = NP
3. **Empirical Evidence**: In practice, 3-SAT instances at the phase transition (around 4.27 clauses per variable) require exponential time with all known algorithms
4. **Community Consensus**: The overwhelming majority of complexity theorists believe P ≠ NP

## The Complexity Gap

### Search Space Structure

For a 3-CNF formula with n variables:

| Aspect | Count | Complexity |
|--------|-------|------------|
| **Possible truth assignments** | 2ⁿ | Exponential |
| **Clauses to verify** | m | Polynomial |
| **Verification time per assignment** | O(m) | Polynomial |
| **Exhaustive search** | O(2ⁿ · m) | Exponential |

A polynomial-time algorithm would need to avoid checking all 2ⁿ assignments while still guaranteeing correctness.

### Why Pruning Cannot Help in General

Modern SAT solvers use sophisticated pruning (unit propagation, clause learning, CDCL). Despite this:
- They work well on **structured** instances (those arising in practice)
- They still require exponential time in the worst case
- There are known hard instances (random 3-CNF at the phase transition) that defeat all known heuristics

## Author's Own Acknowledgment

The most direct evidence of failure is the **withdrawal of the paper itself**. The author's note "a revision has been developed" indicates:

1. The author recognized a flaw in their argument
2. The flaw was significant enough to require withdrawal rather than just a correction
3. No corrected version was ever published, suggesting the flaw was fundamental

This is a self-acknowledged failure — stronger evidence than any external refutation.

## Pattern of Similar Attempts

This attempt follows a common pattern:
1. Claim a polynomial-time algorithm for an NP-complete problem
2. Assert correctness and polynomial time without fully rigorous proof
3. Submit to arXiv (not peer-reviewed)
4. Withdraw when flaws are discovered (by author or community)

The Woeginger list documents hundreds of such attempts, all ultimately flawed.

## What a Correct Proof Would Need

A genuine polynomial-time algorithm for 3-SAT would need to:
1. **Specify** a concrete algorithm (pseudocode or formal description)
2. **Prove correctness**: For ALL 3-CNF formulas, the algorithm correctly decides satisfiability
3. **Prove polynomial time**: The runtime is O(nᵏ) for some fixed constant k
4. **Withstand community scrutiny**: Published in a peer-reviewed venue and verified by experts

Mukherjee's paper did not complete this process.

## Formal Refutation

The Lean and Rocq files in this directory formalize:
1. Why 3-SAT cannot be solved in polynomial time (assuming P ≠ NP)
2. The exponential search space that any correct algorithm must navigate
3. Why no known technique can reduce this exponential space to polynomial
4. The structural barrier represented by the Cook-Levin theorem

## Conclusion

Mukherjee's claimed polynomial-time algorithm for 3-SAT is **refuted by the author's own withdrawal**. The fundamental barrier is the NP-completeness of 3-SAT and the (believed) exponential lower bound on any correct decision algorithm. The precise flaw in Mukherjee's argument cannot be determined without access to the withdrawn manuscript.
