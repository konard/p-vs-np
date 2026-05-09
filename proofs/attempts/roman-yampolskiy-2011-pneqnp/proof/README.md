# Forward Proof Formalization: Yampolskiy 2011

**Navigation:** [↑ Back to Attempt Root](../README.md)

---

## Purpose

This directory contains the **forward formalization** of Yampolskiy's claimed proof that HPTSP ∉ P. It follows the original paper's argument step by step, making explicit every claim and showing where the proof breaks down.

## What is Being Formalized

Yampolskiy's argument proceeds as:

1. **Define HPTSP**: A variant of TSP where path costs are replaced by hash values of encoded paths.
2. **Prove HPTSP ∈ NP** (Section 4 of the paper): Given a Hamiltonian cycle as certificate, verification takes O(|V|) time. ✓ **This part is correct and we formalize it.**
3. **Prove HPTSP ∉ P** (Section 5 of the paper): The avalanche effect prevents pruning, forcing exponential search. ✗ **This part fails — we show where and why.**

## Files

| File | Description |
|------|-------------|
| `lean/YampolskiyProof.lean` | Lean 4 forward formalization |
| `rocq/YampolskiyProof.v` | Rocq (Coq) forward formalization |

## Formalization Status

### Successfully Formalized (What Yampolskiy Got Right)

- **HPTSP definition**: The problem is well-defined. A complete graph, a hash function, and a lexicographic bound determine the decision problem.
- **HPTSP ∈ NP**: The verification algorithm runs in polynomial time O(|V|):
  1. Parse certificate: O(|V|)
  2. Check valid Hamiltonian cycle: O(|V|)
  3. Verify edge costs: O(|V|)
  4. Compute hash: O(|V|)
  5. Lexicographic comparison: O(1)

### Cannot Be Formalized (Where Yampolskiy's Proof Fails)

The following steps in Yampolskiy's argument cannot be proven without unjustified axioms:

| Step | Paper's Claim | Why It Fails |
|------|--------------|--------------|
| Hash SAC | "Avalanche effect prevents local information" | Not a mathematical theorem; statistical property of specific functions |
| No local info | "Sub-path hash tells nothing about full path hash" | Cannot be formally stated as a deterministic property |
| No pruning | "Therefore no pruning is possible" | Even if true, does not exclude non-pruning polynomial algorithms |
| Must check all | "Must examine all V! paths" | Non-sequitur: absence of one approach ≠ no polynomial approach exists |
| Exponential LB | "Therefore HPTSP requires exponential time" | Not derivable from the above; no proper lower bound technique used |

## Key Insight

The formalization reveals that Yampolskiy confuses:
- **"No pruning-based approach works"** (plausible conjecture)
- **"No polynomial-time algorithm exists"** (what needs to be proven)

These are fundamentally different statements. To prove the latter, one needs:
- A reduction from a known NP-hard problem, OR
- A diagonalization argument, OR
- A circuit lower bound argument, OR
- Some other rigorous lower bound technique

The paper provides none of these.

## Navigation

- **Refutation**: See [`../refutation/`](../refutation/) for formal proofs of why Yampolskiy's argument fails.
- **Original paper**: See [`../original/`](../original/) for the paper text and our reconstruction.
