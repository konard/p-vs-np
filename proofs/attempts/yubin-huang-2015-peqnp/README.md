# Yubin Huang (2015) - P=NP Proof Attempt

**Attempt ID**: 105 (from Woeginger's list)
**Author**: Yubin Huang
**Year**: 2015
**Claim**: P = NP
**Source**: [PeerJ Preprints](https://peerj.com/preprints/1455/)

## Summary

In October 2015, Yubin Huang published "Testing a new idea to solve the P = NP problem with mathematical induction" as a PeerJ Preprint. The paper attempts to prove that P = NP by constructing a hierarchy of language classes between P and NP, and showing that every language in NP eventually falls into P through this hierarchy.

The key idea is to use a **filter function** C(M,w) that counts the number of nondeterministic configurations in the shortest accepting computation path of a nondeterministic Turing machine M on input w. By limiting this count, Huang defines a hierarchy of classes Li, where each class contains languages with at most i nondeterministic moves.

## Main Argument

### Key Definitions

1. **Filter Function C(M,w)**: For a nondeterministic Turing machine M and input w, C(M,w) is the number of configurations that have more than one child (i.e., nondeterministic moves) in the shortest accept computation path.

2. **Language Classes Li(M)**: For a nondeterministic Turing machine M accepting language L(M), the subset Li(M) consists of all inputs w where C(M,w) ≤ i.

3. **Hierarchy Li**: The i-th level of the hierarchy is Li = {Li(M) | M is a nondeterministic TM accepting an NP language}.

### Proof Strategy

Huang's argument proceeds as follows:

1. **Hierarchy Construction**: Define a hierarchy L0, L1, L2, ... where Li contains languages decidable with at most i nondeterministic moves.

2. **Deterministic Simulation**: Claim that for each level i, a nondeterministic multi-tape Turing machine can be used to "simulate the (i+1)-th nondeterministic move deterministically in multiple work tapes, to reduce one (the last) nondeterministic move."

3. **Hierarchy Collapse**: Argue that Li+1 ⊆ Li for all i ∈ ℕ.

4. **P = NP Conclusion**: Since:
   - NP = ⋃i∈ℕ Li (every NP language is in some Li)
   - Li ⊆ P for all i (claimed from the hierarchy collapse)
   - Therefore NP ⊆ P
   - Combined with P ⊆ NP, this gives P = NP

### Important Note

The author explicitly notes that this proof attempt does not provide an efficient algorithm for solving NP-complete problems, only a theoretical equivalence.

## The Error

The critical flaw in Huang's argument lies in the **deterministic simulation claim** (Step 2). The argument that one can "simulate the (i+1)-th nondeterministic move deterministically in multiple work tapes" fundamentally misunderstands the nature of nondeterminism.

### Why the Simulation Fails

1. **Exponential Branching**: When a nondeterministic Turing machine makes a nondeterministic choice, it can have exponentially many possible computation paths (up to 2^p(n) paths for polynomial p(n)). "Simulating" this deterministically requires exploring all these paths.

2. **Polynomial Time Bound Violation**: Even if you use multiple work tapes to track different nondeterministic branches, you still need to:
   - Enumerate all possible nondeterministic choices
   - Simulate each branch
   - Check if any branch accepts

   This enumeration itself takes exponential time, not polynomial time.

3. **No Reduction in Complexity**: Moving the "last" nondeterministic move to be handled deterministically doesn't reduce the overall complexity. You're still solving the same hard problem - you've just reorganized when you handle the nondeterminism, not eliminated its computational cost.

4. **False Hierarchy Collapse**: The claim that Li+1 ⊆ Li is unsupported. In fact, adding more nondeterministic moves typically increases the power of the computation model (at least up to polynomial many moves), not decreases it. The languages in Li+1 are potentially more complex than those in Li.

### Fundamental Issue

The error is a **confusion between nondeterministic and deterministic computation models**. The proof essentially assumes that nondeterminism can be "eliminated" one step at a time without increasing time complexity, which is precisely what the P vs NP question asks! This is circular reasoning - it assumes what it's trying to prove.

Specifically:
- If we could deterministically simulate one nondeterministic move in polynomial time, we could iterate this process to simulate all nondeterministic moves.
- But this is equivalent to solving NP problems in polynomial time, which is exactly what P = NP means.
- The proof assumes the ability to do this simulation (implicitly assuming P = NP) to prove P = NP.

## Formalization Goal

This formalization aims to:

1. **Define the hierarchy**: Formalize the Li classes and the filter function C(M,w)
2. **Model the claim**: Express Huang's claim that Li+1 ⊆ Li
3. **Identify the gap**: Show where the "deterministic simulation" step fails or requires unjustified assumptions
4. **Demonstrate the circularity**: Prove that the simulation assumption is equivalent to assuming P = NP

## Related Work

This type of error - attempting to eliminate nondeterminism incrementally without accounting for the exponential blowup - is a common pattern in failed P vs NP proofs. The **relativization barrier** (Baker-Gill-Solovay, 1975) shows that such direct simulation arguments cannot work, as there exist oracles relative to which P ≠ NP.

## References

- Huang, Y. (2015). "Testing a new idea to solve the P = NP problem with mathematical induction". PeerJ Preprints 3:e1455v1. https://peerj.com/preprints/1455/
- Woeginger, G. J. "The P-versus-NP page". Entry #105. https://www.win.tue.nl/~gwoegi/P-versus-NP.htm
- Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP Question". SIAM Journal on Computing, 4(4), 431-442.

## Status

- [x] Folder structure created
- [x] README.md with detailed analysis
- [ ] Coq formalization
- [ ] Lean formalization
- [ ] Isabelle formalization
- [ ] Error documentation complete

## Directory Structure

```
proofs/attempts/yubin-huang-2015-peqnp/
├── README.md (this file)
├── coq/
│   └── YubinHuang2015.v
├── lean/
│   └── YubinHuang2015.lean
└── isabelle/
    └── YubinHuang2015.thy
```
